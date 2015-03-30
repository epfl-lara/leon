package leon.purescala

import Definitions._
import Expressions._
import ExprOps.{preMap, postMap, functionCallsOf}

object DefOps {

  def packageOf(df: Definition): PackageRef = {
    df match {
      case _ : Program => List()
      case u : UnitDef => u.pack 
      case _ => df.owner map packageOf getOrElse List()
    }
  }

  def unitOf(df: Definition): Option[UnitDef] = df match {
    case p : Program => None
    case u : UnitDef => Some(u)
    case other => other.owner flatMap unitOf
  }

  def moduleOf(df: Definition): Option[ModuleDef] = df match {
    case p : Program => None
    case m : ModuleDef => Some(m)
    case other => other.owner flatMap moduleOf
  }

  def programOf(df: Definition): Option[Program] = {
    df match {
      case p : Program => Some(p)
      case other => other.owner flatMap programOf
    }
  }

  def pathFromRoot(df: Definition): List[Definition] ={
    def rec(df : Definition) : List[Definition] = df.owner match {
      case Some(owner) => df :: rec(owner)
      case None => List(df)
    } 
    rec(df).reverse
  }

  def unitsInPackage(p: Program, pack : PackageRef) = p.units filter { _.pack  == pack }

  def isImportedBy(df : Definition, i : Import) : Boolean = 
    i.importedDefs contains df 

  def isImportedBy(df : Definition, is: Seq[Import]) : Boolean =  
    is exists {isImportedBy(df,_)}

  def leastCommonAncestor(df1 : Definition, df2 : Definition) : Definition = {
    (pathFromRoot(df1) zip pathFromRoot(df2))
    .takeWhile{case (df1,df2) => df1 eq df2}
    .last._1
  }


  /** Returns the set of definitions directly visible from the current definition
   *  Definitions that are shadowed by others are not returned.
   */
  def visibleDefsFrom(df : Definition) : Set[Definition] = {
    var toRet = Map[String,Definition]()
    val asList = 
      (pathFromRoot(df).reverse flatMap { _.subDefinitions }) ++ {
        programOf(df) match {
          case None => List()
          case Some(p) => unitsInPackage(p, packageOf(df)) flatMap { _.subDefinitions } 
        }
      } ++
      programOf(df).toList ++
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

  def visibleFunDefsFrom(df: Definition): Set[FunDef] = {
    visibleDefsFrom(df).collect {
      case fd: FunDef => fd
    }
  }

  def funDefsFromMain(p: Program): Set[FunDef] = {
    p.units.filter(_.isMainUnit).toSet.flatMap{ (u: UnitDef) =>
      u.definedFunctions
    }
  }

  def visibleFunDefsFromMain(p: Program): Set[FunDef] = {
    p.units.filter(_.isMainUnit).toSet.flatMap{ (u: UnitDef) =>
      visibleFunDefsFrom(u) ++ u.definedFunctions
    }
  }

  /** Returns true for strict superpackage */ 
  def isSuperPackageOf(p1:PackageRef, p2 : PackageRef) = 
    (p2.length > p1.length) && 
    ( (p1 zip p2 takeWhile { case (n1,n2) => n1 == n2 }).length == p1.length )
    
  def packageAsVisibleFrom(df : Definition, p : PackageRef) = {
    val visiblePacks = 
      packageOf(df) +: (unitOf(df).toSeq.flatMap(_.imports) collect { case PackageImport(pack) => pack })
    val bestSuper = visiblePacks filter { pack => pack == p || isSuperPackageOf(pack,p)} match {
      case Nil => Nil
      case other => other maxBy { _.length }
    }
    p drop bestSuper.length
  }
  
  // This assumes base and target are in the same program
  def pathAsVisibleFrom(base : Definition, target : Definition) : (PackageRef, List[Definition]) = {
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

  def fullName(df: Definition, fromProgram: Option[Program] = None): String = 
    fromProgram orElse programOf(df) match {
      case None => df.id.name
      case Some(p) =>
        val (pr, ds) = pathAsVisibleFrom(p, df)

        (pr ::: ds.flatMap{
          case _: UnitDef => None
          case m: ModuleDef if m.isStandalone => None
          case d => Some(d.id.name)
        }).mkString(".")
    }

  def searchByFullName (
    fullName : String,
    p : Program,
    reliableVisibility : Boolean = true, // Unset this if imports have not yet been set correctly
    exploreStandalones : Boolean = true  // Unset this if your path already includes standalone object names
  ) = searchByFullNameRelative(fullName, p, reliableVisibility,exploreStandalones)
  
  
  def searchByFullNameRelative(
    fullName : String,    
    base : Definition,
    reliableVisibility : Boolean = true, // Unset this if imports have not yet been set correctly
    exploreStandalones : Boolean = true  // Unset this if your path already includes standalone object names
  ) : Option[Definition] = {
  
    require(programOf(base).isDefined)

    val fullNameList = fullName.split("\\.").toList map scala.reflect.NameTransformer.encode
    require(fullNameList.nonEmpty)
    
    def onCondition[A](cond:Boolean)(body : => Option[A]) : Option[A] = {
      if (cond) body else None
    }
    
    // Find a definition by full name, starting from an another definition
    def descendDefs (df : Definition, path : List[String]) : Option[Definition] = { 
      path match {
        case Nil => Some(df)
        case hd :: tl =>
          // ignore UnitDefs
          val subs = df match {
            case p : Program => p.modules
            case _ => df.subDefinitions
          }          
          for (
            nested <- subs find {_.id.toString == hd}; 
            df <- descendDefs(nested, tl) 
          ) yield df
      }
    }
    
    // First, try to find your way from the visible packages from this def
    // ignoring package nonsense.
    // Skip if unreliable visibility.
    ( for ( 
      startingPoint <- {
        onCondition (reliableVisibility) {
          val visible = visibleDefsFrom(base).toList
          val defs : List[Definition] = 
            if(exploreStandalones) 
              visible ++ visible.collect { case ModuleDef(_, subs, true) => subs}.flatten
            else visible
          defs find { _.id.toString == fullNameList.head }
        }
      };
      path = fullNameList.tail;
      df <- descendDefs(startingPoint,path) 
    ) yield df ) orElse {

      val program = programOf(base).get
      val currentPack = packageOf(base)
      val knownPacks = program.units map { _.pack }
      // The correct package has the maximum identifiers
    
      // First try to find a correct subpackage of this package
      val subPacks = knownPacks collect { 
        case p if isSuperPackageOf(currentPack, p) =>
          p drop currentPack.length
      }
      
      import scala.util.Try
      val (packagePart, objectPart) = Try {
        // Find the longest match, then re-attach the current package.
        val pack = subPacks filter { fullNameList.startsWith(_) } maxBy(_.length)
        ( currentPack ++ pack, fullNameList drop pack.length )
      } orElse { Try {
        // In this case, try to find a package that fits beginning from the root package
        val pack = knownPacks filter { fullNameList.startsWith(_) } maxBy(_.length)
        (pack, fullNameList drop pack.length)
      }} getOrElse {
        // No package matches
        (Nil, fullNameList)
      }
      
      if(objectPart.isEmpty) 
        // Probably just a package path, or an object imported from a Scala library,
        // so no definition returned
        None
      else {     
        val point = program.modules find { mod => 
          mod.id.toString == objectPart.head && 
          packageOf(mod)  == packagePart
        } orElse {
          onCondition (exploreStandalones) {
            // Search in standalone objects
            program.modules.collect {
              case ModuleDef(_,subDefs,true) => subDefs 
            }.flatten.find { df =>
              df.id.toString == objectPart.head && 
              packageOf(df)  == packagePart 
            }
          }
        }
    
        for (
          startingPoint <- point;
          path = objectPart.tail;
          df <- descendDefs(startingPoint,path) 
        ) yield df
      }
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
        modules = for (m <- u.modules) yield {
          m.copy(defs = for (df <- m.defs) yield {
            df match {
              case f : FunDef =>
                val newF = fdMap(f)
                newF.fullBody = replaceCalls(newF.fullBody)
                newF
              case c : ClassDef =>
                // val oldMethods = c.methods
                // c.clearMethods()
                // for (m <- oldMethods) {
                //  c.registerMethod(functionToFunction.get(m).map{_.to}.getOrElse(m))
                // }
                c
              case d =>
                d
            }
          })
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
        modules = for (m <- u.modules) yield {
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