/* Copyright 2009-2015 EPFL, Lausanne */

package leon.purescala

import Definitions._
import Expressions._
import ExprOps.{preMap, functionCallsOf}

object DefOps {

  private def packageOf(df: Definition)(implicit pgm: Program): PackageRef = {
    df match {
      case _ : Program => List()
      case u : UnitDef => u.pack
      case _ => unitOf(df).map(_.pack).getOrElse(List())
    }
  }

  private def unitOf(df: Definition)(implicit pgm: Program): Option[UnitDef] = df match {
    case p : Program => None
    case u : UnitDef => Some(u)
    case other => pgm.units.find(_.containsDef(df))
  }

  def moduleOf(df: Definition)(implicit pgm: Program): Option[ModuleDef] = df match {
    case p : Program => None
    case u : UnitDef => None
    case other => pgm.units.flatMap(_.modules).find { _.containsDef(df) }
  }

  def pathFromRoot(df: Definition)(implicit pgm: Program): List[Definition] = {
    def rec(from: Definition): List[Definition] = {
      from :: (if (from == df) {
        Nil
      } else {
        from.subDefinitions.find { sd => (sd eq df) || sd.containsDef(df) } match {
          case Some(sd) =>
            rec(sd)
          case None =>
            Nil
        }
      })
    }
    rec(pgm)
  }

  def unitsInPackage(p: Program, pack: PackageRef) = p.units filter { _.pack  == pack }



  /** Returns the set of definitions directly visible from the current definition
   *  Definitions that are shadowed by others are not returned.
   */
  def visibleDefsFrom(df: Definition)(implicit pgm: Program): Set[Definition] = {
    var toRet = Map[String,Definition]()
    val asList = 
      (pathFromRoot(df).reverse flatMap { _.subDefinitions }) ++ {
        unitsInPackage(pgm, packageOf(df)) flatMap { _.subDefinitions } 
      } ++
      List(pgm) ++
      ( for ( u <- unitOf(df).toSeq;
              imp <- u.imports;
              impDf <- imp.importedDefs(u)
            ) yield impDf
      )
    for (
      df <- asList;
      name = df.id.toString
    ) {
      if (!(toRet contains name)) toRet += name -> df
    }
    toRet.values.toSet
  }

  def visibleFunDefsFrom(df: Definition)(implicit pgm: Program): Set[FunDef] = {
    visibleDefsFrom(df).collect {
      case fd: FunDef => fd
    }
  }

  def funDefsFromMain(implicit pgm: Program): Set[FunDef] = {
    pgm.units.filter(_.isMainUnit).toSet.flatMap{ (u: UnitDef) =>
      u.definedFunctions
    }
  }

  def visibleFunDefsFromMain(implicit p: Program): Set[FunDef] = {
    p.units.filter(_.isMainUnit).toSet.flatMap{ (u: UnitDef) =>
      visibleFunDefsFrom(u) ++ u.definedFunctions
    }
  }


  def fullNameFrom(of: Definition, from: Definition, useUniqueIds: Boolean)(implicit pgm: Program): String = {
    val pathFrom = pathFromRoot(from).dropWhile(_.isInstanceOf[Program])

    val namesFrom = pathToNames(pathFrom, useUniqueIds)
    val namesOf   = pathToNames(pathFromRoot(of), useUniqueIds)

    def stripPrefix(off: List[String], from: List[String]) = {
      val commonPrefix = (off zip from).takeWhile(p => p._1 == p._2)

      val res = off.drop(commonPrefix.size)

      if (res.isEmpty) {
        if (off.isEmpty) List()
        else List(off.last)
      } else {
        res
      }
    }

    val sp = stripPrefix(namesOf, namesFrom)
    if (sp.isEmpty) return "**** " + of.id.uniqueName
    var names: Set[List[String]] = Set(namesOf, stripPrefix(namesOf, namesFrom))

    pathFrom match {
      case (u: UnitDef) :: _ =>
        val imports = u.imports.map {
          case Import(path, true) => path
          case Import(path, false) => path.init
        }.toList

        def stripImport(of: List[String], imp: List[String]): Option[List[String]] = {
          if (of.startsWith(imp)) {
            Some(stripPrefix(of, imp))
          } else {
            None
          }
        }

        for (imp <- imports) {
          names ++= stripImport(namesOf, imp)
        }

      case _ =>
    }

    names.toSeq.minBy(_.size).mkString(".")
  }

  def pathToNames(path: List[Definition], useUniqueIds: Boolean): List[String] = {
    path.flatMap {
      case p: Program =>
        Nil
      case u: UnitDef =>
        u.pack
      case m: ModuleDef if m.isPackageObject =>
        Nil
      case d =>
        if (useUniqueIds) {
          List(d.id.uniqueName)
        } else {
          List(d.id.toString)
        }
    }
  }

  def pathToString(path: List[Definition], useUniqueIds: Boolean): String = {
    pathToNames(path, useUniqueIds).mkString(".")
  }

  def fullName(df: Definition, useUniqueIds: Boolean = false)(implicit pgm: Program): String = {
    pathToString(pathFromRoot(df), useUniqueIds)
  }

  def qualifiedName(fd: FunDef, useUniqueIds: Boolean = false)(implicit pgm: Program): String = {
    pathToString(pathFromRoot(fd).takeRight(2), useUniqueIds)
  }

  private def nameToParts(name: String) = {
    name.split("\\.").toList
  }

  def searchWithin(name: String, within: Definition): Seq[Definition] = {
    searchWithin(nameToParts(name), within)
  }

  def searchWithin(ns: List[String], within: Definition): Seq[Definition] = {
    (ns, within) match {
      case (ns, p: Program) =>
        p.units.flatMap { u =>
          searchWithin(ns, u)
        }

      case (ns, u: UnitDef) =>
        if (ns.startsWith(u.pack)) {
          val rest = ns.drop(u.pack.size)

          u.defs.flatMap { 
            case d: ModuleDef if d.isPackageObject =>
              searchWithin(rest, d)

            case d =>
              rest match {
                case n :: ns =>
                  if (d.id.name == n) {
                    searchWithin(ns, d)
                  } else {
                    Nil
                  }
                case Nil =>
                  List(u)
              }
          }
        } else {
          Nil
        }

      case (Nil, d) => List(d)
      case (n :: ns, d) =>
        d.subDefinitions.filter(_.id.name == n).flatMap { sd =>
          searchWithin(ns, sd)
        }
    }
  }

  def searchRelative(name: String, from: Definition)(implicit pgm: Program): Seq[Definition] = {
    val names = nameToParts(name)
    val path = pathFromRoot(from)

    searchRelative(names, path.reverse)
  }

  private def resolveImports(imports: Seq[Import], names: List[String]): Seq[List[String]] = {
    def resolveImport(i: Import): Option[List[String]] = {
      if (!i.isWild && names.startsWith(i.path.last)) {
        Some(i.path ++ names.tail)
      } else if (i.isWild) {
        Some(i.path ++ names)
      } else {
        None
      }
    }

    imports.flatMap(resolveImport)
  }

  private def searchRelative(names: List[String], rpath: List[Definition])(implicit pgm: Program): Seq[Definition] = {
    (names, rpath) match {
      case (n :: ns, d :: ds) =>
        (d match {
          case p: Program =>
            searchWithin(names, p)

          case u: UnitDef =>
            val inModules = d.subDefinitions.filter(_.id.name == n).flatMap { sd =>
              searchWithin(ns, sd)
            }

            val namesImported = resolveImports(u.imports, names)
            val nameWithPackage = u.pack ++ names

            val allNames = namesImported :+ nameWithPackage

            allNames.foldLeft(inModules) { _ ++ searchRelative(_, ds) }

          case d =>
            if (n == d.id.name) {
              searchWithin(ns, d)
            } else {
              searchWithin(n :: ns, d)
            }
        }) ++ searchRelative(names, ds)

      case _ =>
        Nil
    }
  }

  private def defaultFiMap(fi: FunctionInvocation, nfd: FunDef): Option[Expr] = (fi, nfd) match {
    case (FunctionInvocation(old, args), newfd) if old.fd != newfd =>
      Some(FunctionInvocation(newfd.typed(old.tps), args))
    case _ =>
      None
  }

  /** Clones the given program by replacing some functions by other functions.
    * 
    * @param p The original program
    * @param fdMapF Given f, returns Some(g) if f should be replaced by g, and None if f should be kept.
    *        May be called once each time a function appears (definition and invocation),
    *        so make sure to output the same if the argument is the same.
    * @param fiMapF Given a previous function invocation and its new function definition, returns the expression to use.
    *               By default it is the function invocation using the new function definition.
    * @return the new program with a map from the old functions to the new functions */
  def replaceFunDefs(p: Program)(fdMapF: FunDef => Option[FunDef],
                                 fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap) = {

    var fdMapCache = Map[FunDef, Option[FunDef]]()
    def fdMap(fd: FunDef): FunDef = {
      if (!(fdMapCache contains fd)) {
        fdMapCache += fd -> fdMapF(fd)
      }

      fdMapCache(fd).getOrElse(fd)
    }


    val newP = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m : ModuleDef =>
            m.copy(defs = for (df <- m.defs) yield {
              df match {
                case f : FunDef =>
                  val newF = fdMap(f)
                  newF
                case d =>
                  d
              }
          })
          case d => d
        }
      )
    })
    for(fd <- newP.definedFunctions) {
      if(ExprOps.exists{ case FunctionInvocation(TypedFunDef(fd, targs), fargs) => fdMapCache(fd) != None case _ => false }(fd.fullBody)) {
        fd.fullBody = replaceFunCalls(fd.fullBody, fdMap, fiMapF)
      }
    }
    (newP, fdMapCache.collect{ case (ofd, Some(nfd)) => ofd -> nfd })
  }

  def replaceFunCalls(e: Expr, fdMapF: FunDef => FunDef, fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap) = {
    preMap {
      case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
        fiMapF(fi, fdMapF(fd)).map(_.setPos(fi))
      case _ =>
        None
    }(e)
  }

  def addDefs(p: Program, cds: Traversable[Definition], after: Definition): Program = {
    var found = false
    val res = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.flatMap {
          case m: ModuleDef =>
            val newdefs = for (df <- m.defs) yield {
              df match {
                case `after` =>
                  found = true
                  after +: cds.toSeq
                case d => Seq(d)
              }
            }

            Seq(m.copy(defs = newdefs.flatten))
          case `after` =>
            found = true
            after +: cds.toSeq
          case d => Seq(d)
        }
      )
    })
    if (!found) {
      println("addDefs could not find anchor definition!")
    }
    res
  }
  
  def addFunDefs(p: Program, fds: Traversable[FunDef], after: FunDef): Program = addDefs(p, fds, after)
  
  def addClassDefs(p: Program, fds: Traversable[ClassDef], after: ClassDef): Program = addDefs(p, fds, after)

  // @Note: This function does not filter functions in classdefs
  def filterFunDefs(p: Program, fdF: FunDef => Boolean): Program = {
    p.copy(units = p.units.map { u =>
      u.copy(
        defs = u.defs.collect {
          case md: ModuleDef =>
            md.copy(defs = md.defs.filter {
              case fd: FunDef => fdF(fd) 
              case d => true
            })

          case cd => cd 
        }
      )
    })
  }

  /**
   * Returns a call graph starting from the given sources, taking into account
   * instantiations of function type parameters,
   * If given limit of explored nodes reached, it returns a partial set of reached TypedFunDefs
   * and the boolean set to "false".
   * Otherwise, it returns the full set of reachable TypedFunDefs and "true"
   */

  def typedTransitiveCallees(sources: Set[TypedFunDef], limit: Option[Int] = None): (Set[TypedFunDef], Boolean) = {
    import leon.utils.SearchSpace.reachable
    reachable(
      sources,
      (tfd: TypedFunDef) => functionCallsOf(tfd.fullBody) map { _.tfd },
      limit
    )
  }

}
