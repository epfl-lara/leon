/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import Common.Identifier
import ExprOps.{preMap, functionCallsOf}
import leon.purescala.Types.AbstractClassType
import leon.purescala.Types._

import scala.collection.mutable.{Map => MutableMap}

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

  private def stripPrefix(off: List[String], from: List[String]): List[String] = {
      val commonPrefix = (off zip from).takeWhile(p => p._1 == p._2)

      val res = off.drop(commonPrefix.size)

      if (res.isEmpty) {
        if (off.isEmpty) List()
        else List(off.last)
      } else {
        res
      }
    }
  
  def simplifyPath(namesOf: List[String], from: Definition, useUniqueIds: Boolean)(implicit pgm: Program) = {
    val pathFrom = pathFromRoot(from).dropWhile(_.isInstanceOf[Program])
    
    val namesFrom = pathToNames(pathFrom, useUniqueIds)
    
    val names: Set[List[String]] = Set(namesOf, stripPrefix(namesOf, namesFrom)) ++
      getNameUnderImports(pathFrom, namesOf)
    
    names.toSeq.minBy(_.size).mkString(".")
  }

  def fullNameFrom(of: Definition, from: Definition, useUniqueIds: Boolean)(implicit pgm: Program): String = {
    val pathFrom = pathFromRoot(from).dropWhile(_.isInstanceOf[Program])

    val namesFrom = pathToNames(pathFrom, useUniqueIds)
    val namesOf   = pathToNames(pathFromRoot(of), useUniqueIds)

    val sp = stripPrefix(namesOf, namesFrom)
    if (sp.isEmpty) return "**** " + of.id.uniqueName
    val names: Set[List[String]] =
      Set(namesOf, stripPrefix(namesOf, namesFrom)) ++ getNameUnderImports(pathFrom, namesOf)

    names.toSeq.minBy(_.size).mkString(".")
  }
  
  private def getNameUnderImports(pathFrom: List[Definition], namesOf: List[String]): Seq[List[String]] = {
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

        for {imp <- imports
             strippedImport <- stripImport(namesOf, imp)
        } yield strippedImport
      case _ =>
        Nil
    }
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

  def replaceDefsInProgram(p: Program)(fdMap: Map[FunDef, FunDef] = Map.empty,
                                       cdMap: Map[ClassDef, ClassDef] = Map.empty): Program = {
    p.copy(units = for (u <- p.units) yield {
      u.copy(defs = u.defs.map {
        case m : ModuleDef =>
          m.copy(defs = for (df <- m.defs) yield {
            df match {
              case cd : ClassDef => cdMap.getOrElse(cd, cd)
              case fd : FunDef => fdMap.getOrElse(fd, fd)
              case d => d
            }
        })
        case cd: ClassDef => cdMap.getOrElse(cd, cd)
        case d => d
      })
    })
  }

  def replaceDefs(p: Program)(fdMapF: FunDef => Option[FunDef],
                              cdMapF: ClassDef => Option[ClassDef],
                              fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap,
                              ciMapF: (CaseClass, CaseClassType) => Option[Expr] = defaultCdMap)
                              : (Program, Map[Identifier, Identifier], Map[FunDef, FunDef], Map[ClassDef, ClassDef]) = {

    val idMap = new utils.Bijection[Identifier, Identifier]
    val cdMap = new utils.Bijection[ClassDef  , ClassDef  ]
    val fdMap = new utils.Bijection[FunDef    , FunDef    ]

    val transformer = new DefinitionTransformer(idMap, fdMap, cdMap) {
      override def transformExpr(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Option[Expr] = expr match {
        case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
          val transformFd = transform(fd)
          if(transformFd != fd)
            fiMapF(fi, transformFd)
          else
            None
          //val nfi = fiMapF(fi, transform(fd)) getOrElse expr
          //Some(super.transform(nfi))
        case cc @ CaseClass(cct, args) =>
          val transformCct = transform(cct).asInstanceOf[CaseClassType]
          if(transformCct != cct)
            ciMapF(cc, transformCct)
          else
            None
          //val ncc = ciMapF(cc, transform(cct).asInstanceOf[CaseClassType]) getOrElse expr
          //Some(super.transform(ncc))
        case _ =>
          None
      }

      override def transformFunDef(fd: FunDef): Option[FunDef] = fdMapF(fd)
      override def transformClassDef(cd: ClassDef): Option[ClassDef] = cdMapF(cd)
    }

    val cdsMap = p.definedClasses.map(cd => cd -> transformer.transform(cd)).toMap
    val fdsMap = p.definedFunctions.map(fd => fd -> transformer.transform(fd)).toMap
    val newP = replaceDefsInProgram(p)(fdsMap, cdsMap)
    (newP, idMap.toMap, fdsMap, cdsMap)
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
                                 : (Program, Map[Identifier, Identifier], Map[FunDef, FunDef], Map[ClassDef, ClassDef]) = {
    replaceDefs(p)(fdMapF, cd => None, fiMapF)
      }

  /** Replaces all function calls by an expression depending on the previous function invocation and the new mapped function */
  def replaceFunCalls(e: Expr, fdMapF: FunDef => FunDef, fiMapF: (FunctionInvocation, FunDef) => Option[Expr] = defaultFiMap): Expr = {
    preMap {
      case me @ MatchExpr(scrut, cases) =>
        Some(MatchExpr(scrut, cases.map(matchcase => matchcase match {
          case mc @ MatchCase(pattern, guard, rhs) => MatchCase(replaceFunCalls(pattern, fdMapF), guard, rhs).copiedFrom(mc)
        })).copiedFrom(me))
      case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
        fiMapF(fi, fdMapF(fd)).map(_.copiedFrom(fi))
      case _ =>
        None
    }(e)
  }

  def replaceFunCalls(p: Pattern, fdMapF: FunDef => FunDef): Pattern = PatternOps.preMap{
    case UnapplyPattern(optId, TypedFunDef(fd, tps), subp) => Some(UnapplyPattern(optId, TypedFunDef(fdMapF(fd), tps), subp))
    case _ => None
  }(p)

  private def defaultCdMap(cc: CaseClass, ccd: CaseClassType): Option[Expr] = (cc, ccd) match {
    case (CaseClass(old, args), newCcd) if old.classDef != newCcd.classDef =>
      Some(CaseClass(newCcd, args))
    case _ =>
      None
  }
  
  /** Clones the given program by replacing some classes by other classes.
    * 
    * @param p The original program
    * @param ciMapF Given a previous case class invocation and its new case class definition, returns the expression to use.
    *               By default it is the case class construction using the new case class definition.
    * @return the new program with a map from the old case classes to the new case classes, with maps concerning identifiers and function definitions. */
  def replaceCaseClassDefs(p: Program)(cdMapFOriginal: CaseClassDef => Option[Option[AbstractClassType] => CaseClassDef],
                                       ciMapF: (CaseClass, CaseClassType) => Option[Expr] = defaultCdMap)
                                       : (Program, Map[ClassDef, ClassDef], Map[Identifier, Identifier], Map[FunDef, FunDef]) = {
    var cdMapFCache = Map[CaseClassDef, Option[Option[AbstractClassType] => CaseClassDef]]()
    var cdMapCache = Map[ClassDef, Option[ClassDef]]()
    var idMapCache = Map[Identifier, Identifier]()
    var fdMapFCache = Map[FunDef, Option[FunDef]]()
    var fdMapCache = Map[FunDef, Option[FunDef]]()

    def cdMapF(cd: ClassDef): Option[Option[AbstractClassType] => CaseClassDef] = {
      cd match {
        case ccd: CaseClassDef =>
          cdMapFCache.getOrElse(ccd, {
            val new_cd_potential = cdMapFOriginal(ccd)
            cdMapFCache += ccd -> new_cd_potential
            new_cd_potential
          })
        case acd: AbstractClassDef => None
      }
    }

    def tpMap[T <: TypeTree](tt: T): T = TypeOps.postMap{
      case AbstractClassType(asd, targs) => Some(AbstractClassType(cdMap(asd).asInstanceOf[AbstractClassDef], targs))
      case CaseClassType(ccd, targs) => Some(CaseClassType(cdMap(ccd).asInstanceOf[CaseClassDef], targs))
      case e => None
    }(tt).asInstanceOf[T]

    def duplicateClassDef(cd: ClassDef): ClassDef = {
      cdMapCache.get(cd) match {
        case Some(new_cd) => 
          new_cd.get // None would have meant that this class would never be duplicated, which is not possible.
        case None =>
          val parent = cd.parent.map(duplicateAbstractClassType)
          val new_cd = cdMapF(cd).map(f => f(parent)).getOrElse {
            cd match {
              case acd:AbstractClassDef => acd.duplicate(parent = parent)
              case ccd:CaseClassDef => 
                ccd.duplicate(parent = parent, fields = ccd.fieldsIds.map(id => ValDef(idMap(id)))) // Should not cycle since fields have to be abstract.
            }
          }
          cdMapCache += cd -> Some(new_cd)
          new_cd
      }
    }

    def duplicateAbstractClassType(act: AbstractClassType): AbstractClassType = {
      TypeOps.postMap{
        case AbstractClassType(acd, tps) => Some(AbstractClassType(duplicateClassDef(acd).asInstanceOf[AbstractClassDef], tps))
        case CaseClassType(ccd, tps) => Some(CaseClassType(duplicateClassDef(ccd).asInstanceOf[CaseClassDef], tps))
        case _ => None
      }(act).asInstanceOf[AbstractClassType]
    }

    // If at least one descendants or known case class needs conversion, then all the hierarchy will be converted.
    // If something extends List[A] and A is modified, then the first something should be modified.
    def dependencies(s: ClassDef): Set[ClassDef] = {
      leon.utils.fixpoint((s: Set[ClassDef]) => s ++ s.flatMap(_.knownDescendants) ++ s.flatMap(_.parent.toList.flatMap(p => TypeOps.collect[ClassDef]{
        case AbstractClassType(acd, _) => Set(acd:ClassDef) ++ acd.knownDescendants
        case CaseClassType(ccd, _) => Set(ccd:ClassDef)
        case _ => Set()
      }(p))))(Set(s))
    }

    def cdMap(cd: ClassDef): ClassDef = {
      cdMapCache.get(cd) match {
        case Some(Some(new_cd)) => new_cd
        case Some(None) => cd
        case None =>
          if(cdMapF(cd).isDefined || dependencies(cd).exists(cd => cdMapF(cd).isDefined)) { // Needs replacement in any case.
            duplicateClassDef(cd)
          } else {
            cdMapCache += cd -> None
          }
          cdMapCache(cd).getOrElse(cd)
      }
    }

    def idMap(id: Identifier): Identifier = {
      if (!(idMapCache contains id)) {
        val new_id = id.duplicate(tpe = tpMap(id.getType))
        idMapCache += id -> new_id
      }
      idMapCache(id)
    }

    def idHasToChange(id: Identifier): Boolean = {
      typeHasToChange(id.getType)
    }

    def typeHasToChange(tp: TypeTree): Boolean = {
      TypeOps.exists{
        case AbstractClassType(acd, _) => cdMap(acd) != acd
        case CaseClassType(ccd, _) => cdMap(ccd) != ccd
        case _ => false
      }(tp)
    }

    def patternHasToChange(p: Pattern): Boolean = {
      PatternOps.exists {
        case CaseClassPattern(optId, cct, sub) => optId.exists(idHasToChange) || typeHasToChange(cct)
        case InstanceOfPattern(optId, cct) => optId.exists(idHasToChange) || typeHasToChange(cct)
        case Extractors.Pattern(optId, subp, builder) => optId.exists(idHasToChange)
        case e => false
      } (p)
    }

    def exprHasToChange(e: Expr): Boolean = {
      ExprOps.exists{
        case Let(id, expr, body) => idHasToChange(id)
        case Variable(id) => idHasToChange(id)
        case ci @ CaseClass(cct, args) => typeHasToChange(cct)
        case CaseClassSelector(cct, expr, identifier) => typeHasToChange(cct) || idHasToChange(identifier)
        case IsInstanceOf(e, cct) => typeHasToChange(cct)
        case AsInstanceOf(e, cct) => typeHasToChange(cct)
        case MatchExpr(scrut, cases) => 
          cases.exists{ 
            case MatchCase(pattern, optGuard, rhs) =>
              patternHasToChange(pattern)
          }
        case fi @ FunctionInvocation(TypedFunDef(fd, tps), args) =>
          tps.exists(typeHasToChange)
        case _ =>
          false
      }(e)
    }

    def funDefHasToChange(fd: FunDef): Boolean = {
      exprHasToChange(fd.fullBody) || fd.params.exists(vid => typeHasToChange(vid.id.getType)) || typeHasToChange(fd.returnType)
    }

    def funHasToChange(fd: FunDef): Boolean = {
      funDefHasToChange(fd) || p.callGraph.transitiveCallees(fd).exists(fd =>
        fdMapFCache.get(fd) match {
          case Some(Some(_)) => true
          case Some(None) => false
          case None => funDefHasToChange(fd)
        })
    }

    def fdMapFCached(fd: FunDef): Option[FunDef] = {
      fdMapFCache.get(fd) match {
        case Some(e) => e
        case None =>
          val new_fd = if(funHasToChange(fd)) {
            Some(fd.duplicate(params = fd.params.map(vd => ValDef(idMap(vd.id))), returnType = tpMap(fd.returnType)))
          } else {
            None
          }
          fdMapFCache += fd -> new_fd
          new_fd
      }
    }

    def duplicateParents(fd: FunDef): Unit = {
      fdMapCache.get(fd) match {
        case None =>
          fdMapCache += fd -> fdMapFCached(fd).orElse(Some(fd.duplicate()))
          for(fp <- p.callGraph.callers(fd)) {
            duplicateParents(fp)
          }
        case _ =>
      }
    }

    def fdMap(fd: FunDef): FunDef = {
      fdMapCache.get(fd) match {
        case Some(Some(e)) => e
        case Some(None) => fd
        case None =>
          if(fdMapFCached(fd).isDefined || p.callGraph.transitiveCallees(fd).exists(fd => fdMapFCached(fd).isDefined))  {
            duplicateParents(fd)
          } else {
            fdMapCache += fd -> None
          }
          fdMapCache(fd).getOrElse(fd)
      }
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

    def replaceClassDefUse(e: Pattern): Pattern = PatternOps.postMap{
      case CaseClassPattern(optId, cct, sub) => Some(CaseClassPattern(optId.map(idMap), tpMap[CaseClassType](cct), sub))
      case InstanceOfPattern(optId, cct) => Some(InstanceOfPattern(optId.map(idMap), tpMap[ClassType](cct)))
      case UnapplyPattern(optId, TypedFunDef(fd, tps), subp) => Some(UnapplyPattern(optId.map(idMap), TypedFunDef(fdMap(fd), tps.map(tpMap)), subp))
      case Extractors.Pattern(Some(id), subp, builder) => Some(builder(Some(idMap(id)), subp))
      case e => None
    }(e)

    def replaceClassDefsUse(e: Expr): Expr = {
      ExprOps.postMap {
        case Let(id, expr, body) => Some(Let(idMap(id), expr, body))
        case Lambda(vd, body) => Some(Lambda(vd.map(vd => ValDef(idMap(vd.id))), body))
        case Variable(id) => Some(Variable(idMap(id)))
        case ci @ CaseClass(ct, args) =>
          ciMapF(ci, tpMap(ct)).map(_.setPos(ci))
        case CaseClassSelector(cct, expr, identifier) =>
          val new_cct = tpMap(cct)
          val selection = if (new_cct != cct || new_cct.classDef.fieldsIds != cct.classDef.fieldsIds) idMap(identifier) else identifier
          Some(CaseClassSelector(new_cct, expr, selection))
        case IsInstanceOf(e, ct) => Some(IsInstanceOf(e, tpMap(ct)))
        case AsInstanceOf(e, ct) => Some(AsInstanceOf(e, tpMap(ct)))
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

    for (fd <- newP.definedFunctions) {
      if (fdMapCache.getOrElse(fd, None).isDefined) {
        fd.fullBody = replaceClassDefsUse(fd.fullBody)
      }
    }

    // make sure classDef invariants are correctly assigned to transformed classes
    for ((cd, optNew) <- cdMapCache; newCd <- optNew; inv <- newCd.invariant) {
      newCd.setInvariant(fdMap(inv))
    }

    (newP,
        cdMapCache.collect{case (cd, Some(new_cd)) => cd -> new_cd},
        idMapCache,
        fdMapCache.collect{case (cd, Some(new_cd)) => cd -> new_cd })
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
      println(s"addDefs could not find anchor definition! Not found: $after")
      p.definedFunctions.filter(f => f.id.name == after.id.name).map(fd => fd.id.name + " : " + fd) match {
        case Nil => 
        case e => println("Did you mean " + e)
    }
      println(Thread.currentThread().getStackTrace.map(_.toString).take(10).mkString("\n"))
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

  def augmentCaseClassFields(extras: Seq[(CaseClassDef, Seq[(ValDef, Expr)])])
                            (program: Program) = {

    def updateBody(body: Expr): Expr = {
      preMap({
        case CaseClass(ct, args) => extras.find(p => p._1 == ct.classDef).map{
          case (ccd, extraFields) =>
            CaseClass(CaseClassType(ccd, ct.tps), args ++ extraFields.map{ case (_, v) => v })
        }
        case _ => None
      })(body)
    }

    extras.foreach{ case (ccd, extraFields) => ccd.setFields(ccd.fields ++ extraFields.map(_._1)) }
    for {
      fd <- program.definedFunctions
    } {
      fd.body = fd.body.map(body => updateBody(body))
      fd.precondition = fd.precondition.map(pre => updateBody(pre))
      fd.postcondition = fd.postcondition.map(post => updateBody(post))
    }
  }

}
