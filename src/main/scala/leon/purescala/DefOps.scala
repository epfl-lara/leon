/* Copyright 2009-2015 EPFL, Lausanne */

package leon.purescala

import Definitions._
import Expressions._
import ExprOps.{preMap, postMap, functionCallsOf}

object DefOps {

  def packageOf(df: Definition)(implicit pgm: Program): PackageRef = {
    df match {
      case _ : Program => List()
      case u : UnitDef => u.pack
      case _ => unitOf(df).map(_.pack).getOrElse(List())
    }
  }

  def unitOf(df: Definition)(implicit pgm: Program): Option[UnitDef] = df match {
    case p : Program => None
    case u : UnitDef => Some(u)
    case other => pgm.units.find(_.containsDef(df))
  }

  def moduleOf(df: Definition)(implicit pgm: Program): Option[ModuleDef] = df match {
    case p : Program => None
    case m : ModuleDef => Some(m)
    case other => unitOf(df).flatMap { u =>
      u.modules.find(_.containsDef(df))
    }
  }

  def pathFromRoot(df: Definition)(implicit pgm: Program): List[Definition] ={
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

  /** Returns true for strict superpackage */ 
  /*
  def isSuperPackageOf(p1:PackageRef, p2 : PackageRef) = {
    (p2.length > p1.length) &&
    ( (p1 zip p2 takeWhile { case (n1,n2) => n1 == n2 }).length == p1.length )
  }

  def packageAsVisibleFrom(df: Definition, p: PackageRef)(implicit pgm: Program) = {
    val visiblePacks = 
      packageOf(df) +: (unitOf(df).toSeq.flatMap(_.imports) collect { case PackageImport(pack) => pack })
    val bestSuper = visiblePacks filter { pack => pack == p || isSuperPackageOf(pack,p)} match {
      case Nil => Nil
      case other => other maxBy { _.length }
    }
    p drop bestSuper.length
  }
  */

  
  def fullNameFrom(of: Definition, from: Definition)(implicit pgm: Program): String = {
    val pathFrom = pathFromRoot(from).dropWhile(_.isInstanceOf[Program])

    val namesFrom = pathToNames(pathFrom)
    val namesOf   = pathToNames(pathFromRoot(of))

    def stripPrefix(of: List[String], from: List[String]) = {
      val removePrefix = (of zip from).dropWhile(p => p._1 == p._2).map(_._1)
      if (removePrefix.size == 0) {
        List(from.last)
      } else {
        removePrefix
      }
    }

    var names: Set[List[String]] = Set(namesOf, stripPrefix(namesOf, namesOf))

    pathFrom match {
      case (u: UnitDef) :: _ =>
        val imports = u.imports.map {
          case PackageImport(ls) => (ls, true)
          case SingleImport(d)   => (nameToParts(fullName(d)), false)
          case WildcardImport(d) => (nameToParts(fullName(d)), true)
        }.toList

        def stripImport(of: List[String], imp: List[String], isWild: Boolean): Option[List[String]] = {
          if (of.startsWith(imp)) {
            if (isWild) {
              Some(of.drop(imp.size-1))
            } else {
              Some(of.drop(imp.size-2))
            }
          } else {
            None
          }
        }

        for ((imp, isWild) <- imports) {
          names ++= stripImport(namesOf, imp, isWild)
        }

      case _ =>
    }

    names.toSeq.minBy(_.size).mkString(".")
  }

  /*
  private def pathAsVisibleFrom(base: Definition, target: Definition)(implicit pgm: Program): (PackageRef, List[Definition]) = {
    val rootPath = pathFromRoot(target)
    val ancestor = leastCommonAncestor(base, target)
    val pth = rootPath dropWhile { _.owner != Some(ancestor) }
    val pathFromAncestor = if (pth.isEmpty) List(target) else pth
    val index = rootPath lastIndexWhere { isImportedBy(_, unitOf(base).toSeq.flatMap { _.imports }) }
    val pathFromImport = rootPath drop scala.math.max(index, 0)
    val finalPath = if (pathFromAncestor.length <= pathFromImport.length) pathFromAncestor else pathFromImport
    assert(finalPath.nonEmpty)
    
    // Package 
    val pack = if (finalPath.head.isInstanceOf[UnitDef]) {
      packageAsVisibleFrom(base, packageOf(target))
    }
    else Nil
      
    (pack, finalPath)
  }
  */

  def pathToNames(path: List[Definition]): List[String] = {
    path.flatMap {
      case p: Program =>
        Nil
      case u: UnitDef =>
        u.pack
      case m: ModuleDef if m.isPackageObject =>
        Nil
      case d =>
        List(d.id.name)
    }
  }

  def pathToString(path: List[Definition]): String = {
    pathToNames(path).mkString(".")
  }

  def fullName(df: Definition)(implicit pgm: Program): String = {
    pathToString(pathFromRoot(df))
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

  /*
   * Apply an expression operation on all expressions contained in a FunDef
   */
  def applyOnFunDef(operation : Expr => Expr)(funDef : FunDef): FunDef = {
    val newFunDef = funDef.duplicate 
    newFunDef.fullBody = operation(funDef.fullBody)
    newFunDef
  }
    
  /**
   * Apply preMap on all expressions contained in a FunDef
   */
  def preMapOnFunDef(repl : Expr => Option[Expr], applyRec : Boolean = false )(funDef : FunDef) : FunDef = {
    applyOnFunDef(preMap(repl, applyRec))(funDef)  
  }
 
  /**
   * Apply postMap on all expressions contained in a FunDef
   */
  def postMapOnFunDef(repl : Expr => Option[Expr], applyRec : Boolean = false )(funDef : FunDef) : FunDef = {
    applyOnFunDef(postMap(repl, applyRec))(funDef)  
  }

  private def defaultFiMap(fi: FunctionInvocation, nfd: FunDef): Option[FunctionInvocation] = (fi, nfd) match {
    case (FunctionInvocation(old, args), newfd) if old.fd != newfd =>
      Some(FunctionInvocation(newfd.typed(old.tps), args))
    case _ =>
      None
  }

  def replaceFunDefs(p: Program)(fdMapF: FunDef => Option[FunDef],
                                 fiMapF: (FunctionInvocation, FunDef) => Option[FunctionInvocation] = defaultFiMap) = {

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

  def mapFunDefs(e: Expr, fdMap: PartialFunction[FunDef, FunDef]): Expr = {
    preMap {
      case FunctionInvocation(tfd, args) =>
        fdMap.lift.apply(tfd.fd).map {
          nfd => FunctionInvocation(nfd.typed(tfd.tps), args)
        }
      case _ => None
    }(e)
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
