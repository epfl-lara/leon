/* Copyright 2009-2015 EPFL, Lausanne */

package leon.purescala

import Definitions._
import Expressions._
import Common.Identifier
import ExprOps.{preMap, functionCallsOf}
import leon.purescala.Types.AbstractClassType
import leon.purescala.Types._

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
    * @param fiMapF Given a previous function invocation and its new function definition, returns the expression to use.
    *               By default it is the function invocation using the new function definition.
    * @return the new program with a map from the old functions to the new functions */
  def replaceFunDefs(p: Program)(fdMapF: FunDef => Option[FunDef],
                                 fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap)
                                 : (Program, Map[FunDef, FunDef])= {

    var fdMapCache = Map[FunDef, FunDef]()
    def fdMap(fd: FunDef): FunDef = {
      if (!(fdMapCache contains fd)) {
        fdMapCache += fd -> fdMapF(fd).getOrElse(fd.duplicate())
      }

      fdMapCache(fd)
    }


    val newP = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m : ModuleDef =>
            m.copy(defs = for (df <- m.defs) yield {
              df match {
                case f : FunDef => fdMap(f)
                case d => d
              }
          })
          case d => d
        }
      )
    })
    // TODO: Check for function invocations in unapply patterns.
    for(fd <- newP.definedFunctions) {
      if(ExprOps.exists{ case FunctionInvocation(TypedFunDef(fd, targs), fargs) => fdMapCache contains fd case _ => false }(fd.fullBody)) {
        fd.fullBody = replaceFunCalls(fd.fullBody, fdMapCache, fiMapF)
      }
    }
    (newP, fdMapCache)
  }

  def replaceFunCalls(e: Expr, fdMapF: FunDef => FunDef, fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap) = {
    preMap {
      case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
        fiMapF(fi, fdMapF(fd)).map(_.setPos(fi))
      case _ =>
        None
    }(e)
  }
  

  private def defaultCdMap(cc: CaseClass, ccd: CaseClassType): Option[Expr] = (cc, ccd) match {
    case (CaseClass(old, args), newCcd) if old.classDef != newCcd =>
      Some(CaseClass(newCcd, args))
    case _ =>
      None
  }
  
  /** Clones the given program by replacing some classes by other classes.
    * 
    * @param p The original program
    * @param cdMapF Given c and its cloned parent, returns Some(d) if c should be replaced by d, and None if c should be kept.
    *        Will always start to call this method for the topmost parents, and then descending.
    * @param fiMapF Given a previous case class invocation and its new case class definition, returns the expression to use.
    *               By default it is the case class construction using the new case class definition.
    * @return the new program with a map from the old case classes to the new case classes */
  def replaceClassDefs(p: Program)(cdMapF: (ClassDef, Option[AbstractClassType]) => Option[ClassDef],
                                   ciMapF: (CaseClass, CaseClassType) => Option[Expr] = defaultCdMap)
                                   : (Program, Map[ClassDef, ClassDef], Map[Identifier, Identifier], Map[FunDef, FunDef]) = {
    var cdMapCache = Map[ClassDef, ClassDef]()
    var idMapCache = Map[Identifier, Identifier]()
    var fdMapCache = Map[FunDef, FunDef]()
    def tpMap(tt: TypeTree): TypeTree = TypeOps.postMap{
      case AbstractClassType(asd, targs) => Some(AbstractClassType(cdMap(asd).asInstanceOf[AbstractClassDef], targs))
      case CaseClassType(ccd, targs) => Some(CaseClassType(cdMap(ccd).asInstanceOf[CaseClassDef], targs))
      case e => None
    }(tt)
    
    def cdMap(cd: ClassDef): ClassDef = {
      if (!(cdMapCache contains cd)) {
        lazy val parent = cd.parent.map( tpMap(_).asInstanceOf[AbstractClassType] )
        val ncd = cdMapF(cd, parent) match {
          case Some(new_ccd) =>
            for((old_id, new_id) <- cd.fieldsIds.zip(new_ccd.fieldsIds)) {
              idMapCache += old_id -> new_id
            }
            new_ccd
          case None =>
            cd match {
              case acd:AbstractClassDef => acd.duplicate(parent = parent)
              case ccd:CaseClassDef => ccd.duplicate(parent = parent, fields = ccd.fieldsIds.map(id => ValDef(idMap(id)))) // Should not cycle since fields have to be abstract.
            }
        }
        cdMapCache += cd -> ncd
      }
      cdMapCache(cd)
    }
    def idMap(id: Identifier): Identifier = {
      if (!(idMapCache contains id)) {
        idMapCache += id -> id.duplicate(tpe = tpMap(id.getType))
      }
      idMapCache(id)
    }
    def fdMap(fd: FunDef): FunDef = {
      if (!(fdMapCache contains fd)) {
        fdMapCache += fd -> fd.duplicate(params = fd.params.map(vd => ValDef(idMap(vd.id))), returnType = tpMap(fd.returnType))
      }
      fdMapCache(fd)
    }
    
    val newP = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m : ModuleDef =>
            m.copy(defs = for (df <- m.defs) yield {
              df match {
                case cd : ClassDef => cdMap(cd)
                case fd : FunDef => fdMap(fd)
                case d => d
              }
          })
          case d => d
        }
      )
    })
    object ToTransform {
      def unapply(c: ClassType): Option[ClassDef] = Some(cdMap(c.classDef))
    }
    trait Transformed[T <: TypeTree] {
      def unapply(c: T): Option[T] = Some(TypeOps.postMap({
        case c: ClassType =>
          val newClassDef = cdMap(c.classDef)
          Some((c match {
            case CaseClassType(ccd, tps) =>
              CaseClassType(newClassDef.asInstanceOf[CaseClassDef], tps.map(e => TypeOps.postMap{ case TypeTransformed(ct) => Some(ct) case _ => None }(e)))
            case AbstractClassType(acd, tps) =>
              AbstractClassType(newClassDef.asInstanceOf[AbstractClassDef], tps.map(e => TypeOps.postMap{ case TypeTransformed(ct) => Some(ct) case _ => None }(e)))
          }).asInstanceOf[T])
        case _ => None
      })(c).asInstanceOf[T])
    }
    object CaseClassTransformed extends Transformed[CaseClassType]
    object ClassTransformed extends Transformed[ClassType]
    object TypeTransformed extends Transformed[TypeTree]
    def replaceClassDefUse(e: Pattern): Pattern = PatternOps.postMap{
      case CaseClassPattern(optId, CaseClassTransformed(ct), sub) => Some(CaseClassPattern(optId.map(idMap), ct, sub))
      case InstanceOfPattern(optId, ClassTransformed(ct)) => Some(InstanceOfPattern(optId.map(idMap), ct))
      case UnapplyPattern(optId, TypedFunDef(fd, tps), subp) => Some(UnapplyPattern(optId.map(idMap), TypedFunDef(fdMap(fd), tps.map(tpMap)), subp))
      case Extractors.Pattern(Some(id), subp, builder) => Some(builder(Some(idMap(id)), subp))
      case e => None
    }(e)
    
    def replaceClassDefsUse(e: Expr): Expr = {
      ExprOps.postMap {
        case Let(id, expr, body) => Some(Let(idMap(id), expr, body))
        case Variable(id) => Some(Variable(idMap(id)))
        case ci @ CaseClass(CaseClassTransformed(ct), args) =>
          ciMapF(ci, ct).map(_.setPos(ci))
        //case IsInstanceOf(e, ToTransform()) =>
        case CaseClassSelector(CaseClassTransformed(cct), expr, identifier) =>
          Some(CaseClassSelector(cct, expr, idMap(identifier)))
        case IsInstanceOf(e, ClassTransformed(ct)) => Some(IsInstanceOf(e, ct))
        case AsInstanceOf(e, ClassTransformed(ct)) => Some(AsInstanceOf(e, ct))
        case MatchExpr(scrut, cases) => 
          Some(MatchExpr(scrut, cases.map{ 
              case MatchCase(pattern, optGuard, rhs) =>
                MatchCase(replaceClassDefUse(pattern), optGuard, rhs)
            }))
        case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
          defaultFiMap(fi, fdMap(fd)).map(_.setPos(fi))
        case _ =>
          None
      }(e)
    }
    
    for(fd <- newP.definedFunctions) {
      fd.fullBody = replaceClassDefsUse(fd.fullBody)
    }
    (newP, cdMapCache, idMapCache, fdMapCache)
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
