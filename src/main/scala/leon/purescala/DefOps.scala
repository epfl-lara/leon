/* Copyright 2009-2015 EPFL, Lausanne */

package leon.purescala

import Definitions._
import Expressions._
import ExprOps.{preMap, postMap, functionCallsOf}

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

  private def pathFromRoot(df: Definition)(implicit pgm: Program): List[Definition] ={
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
              impDf <- imp.importedDefs
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

    def stripPrefix(of: List[String], from: List[String]) = {
      val commonPrefix = (of zip from).takeWhile(p => p._1 == p._2)

      val res = of.drop(commonPrefix.size)

      if (res.isEmpty) {
        List(of.last)
      } else {
        res
      }
    }

    var names: Set[List[String]] = Set(namesOf, stripPrefix(namesOf, namesFrom))

    pathFrom match {
      case (u: UnitDef) :: _ =>
        val imports = u.imports.map {
          case PackageImport(ls) => ls
          case SingleImport(d)   => nameToParts(fullName(d, useUniqueIds)).init
          case WildcardImport(d) => nameToParts(fullName(d, useUniqueIds))
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
          List(d.id.name)
        }
    }
  }

  def pathToString(path: List[Definition], useUniqueIds: Boolean): String = {
    pathToNames(path, useUniqueIds).mkString(".")
  }

  def fullName(df: Definition, useUniqueIds: Boolean = false)(implicit pgm: Program): String = {
    pathToString(pathFromRoot(df), useUniqueIds)
  }

  private def nameToParts(name: String) = {
    name.split("\\.").toList map scala.reflect.NameTransformer.encode
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

  private case class ImportPath(ls: List[String], wild: Boolean)

  private def resolveImports(imports: List[ImportPath], names: List[String]): List[List[String]] = {
    def resolveImport(i: ImportPath): Option[List[String]] = {
      if (!i.wild && names.startsWith(i.ls.last)) {
        Some(i.ls ++ names.tail)
      } else if (i.wild) {
        Some(i.ls ++ names)
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
            val imports = u.imports.map {
              case PackageImport(ls) => ImportPath(ls, true)
              case SingleImport(d) => ImportPath(nameToParts(fullName(d)), false)
              case WildcardImport(d) => ImportPath(nameToParts(fullName(d)), true)
            }.toList

            val inModules = d.subDefinitions.filter(_.id.name == n).flatMap { sd =>
              searchWithin(ns, sd)
            }

            val namesImported = resolveImports(imports, names)
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

  def replaceFunDefs(p: Program)(fdMapF: FunDef => Option[FunDef],
                                 fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap) = {

    var fdMapCache = Map[FunDef, Option[FunDef]]()
    def fdMap(fd: FunDef): FunDef = {
      if (!(fdMapCache contains fd)) {
        fdMapCache += fd -> fdMapF(fd)
      }

      fdMapCache(fd).getOrElse(fd)
    }

    def replaceCalls(e: Expr): Expr = {
      preMap {
        case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
          fiMapF(fi, fdMap(fd)).map(_.setPos(fi))
        case _ =>
          None
      }(e)
    }

    val newP = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m : ModuleDef =>
            m.copy(defs = for (df <- m.defs) yield {
              df match {
                case f : FunDef =>
                  val newF = fdMap(f)
                  newF.fullBody = replaceCalls(newF.fullBody)
                  newF
                case d =>
                  d
              }
          })
          case d => d
        },
        imports = u.imports map {
          case SingleImport(fd : FunDef) => 
            SingleImport(fdMap(fd))
          case other => other
        }
      )
    })

    (newP, fdMapCache.collect{ case (ofd, Some(nfd)) => ofd -> nfd })
  }

  def addFunDefs(p: Program, fds: Traversable[FunDef], after: FunDef): Program = {
    var found = false
    val res = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m: ModuleDef =>
            val newdefs = for (df <- m.defs) yield {
              df match {
                case `after` =>
                  found = true
                  after +: fds.toSeq
                case d =>
                  Seq(d)
              }
            }

            m.copy(defs = newdefs.flatten)
          case d => d
        }
      )
    })
    if (!found) {
      println("addFunDefs could not find anchor function!")
    }
    res
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
