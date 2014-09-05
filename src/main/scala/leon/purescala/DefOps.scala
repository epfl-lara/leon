package leon.purescala

import Common._
import Definitions._

object DefOps {
  
  def inPackage(df : Definition) : PackageRef = {
    df match {
      case _ : Program => List()
      case u : UnitDef => u.pack 
      case _ => inPackage(df.owner.get)
    }
  }
  
  def inUnit(df : Definition) : Option[UnitDef] = df match {
    case p : Program => None
    case u : UnitDef => Some(u)
    case other => other.owner flatMap inUnit
  }
  
  def inProgram(df : Definition) : Program = {
    df match {
      case p : Program => p
      case other => inProgram(other.owner.get)
    }
  }
    
  def pathFromRoot (df : Definition): List[Definition] ={
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
      (pathFromRoot(df).reverse flatMap { _.subDefinitions })  ++
      (unitsInPackage(inProgram(df), inPackage(df)) flatMap { _.subDefinitions } ) ++
      Seq(inProgram(df)) ++
      ( for ( u <- inUnit(df).toSeq;
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

  /** Returns true for strict superpackage */ 
  def isSuperPackageOf(p1:PackageRef, p2 : PackageRef) = 
    (p2.length > p1.length) && 
    ( (p1 zip p2 takeWhile { case (n1,n2) => n1 == n2 }).length == p1.length )
    
  def packageAsVisibleFrom(df : Definition, p : PackageRef) = {
    val visiblePacks = 
      inPackage(df) +: (inUnit(df).toSeq.flatMap(_.imports) collect { case PackageImport(pack) => pack })
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
    val index = rootPath lastIndexWhere { isImportedBy(_,inUnit(base).toSeq.flatMap { _.imports }) }
    val pathFromImport = rootPath drop scala.math.max(index, 0)
    val finalPath = if (pathFromAncestor.length <= pathFromImport.length) pathFromAncestor else pathFromImport
    assert(!finalPath.isEmpty)
    
    // Package 
    val pack = if (finalPath.head.isInstanceOf[UnitDef]) {
      packageAsVisibleFrom(base, inPackage(target))
    }
    else Nil
      
    (pack, finalPath)
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
  
    val fullNameList = fullName.split("\\.").toList map scala.reflect.NameTransformer.encode
    require(!fullNameList.isEmpty)
    
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
              visible ++ (visible.collect{ case ModuleDef(_,subs,true) => subs }.flatten)
            else visible
          defs find { _.id.toString == fullNameList.head }
        }
      };
      path = fullNameList.tail;
      df <- descendDefs(startingPoint,path) 
    ) yield df ) orElse {
      
      // Now starts the package nonsense
      def isPrefixOf[A](pre : List[A],l : List[A]) : Boolean = (pre,l) match {
        case (Nil, _) => true
        case (hp :: tp, hl :: tl) if hp == hl => isPrefixOf(tp,tl)
        case _ => false
      }

      val program = inProgram(base)
      val currentPack = inPackage(base)
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
        val pack = subPacks filter { isPrefixOf(_,fullNameList) } maxBy(_.length)
        ( currentPack ++ pack, fullNameList drop pack.length )
      } orElse { Try {
        // In this case, try to find a package that fits beginning from the root package
        val pack = knownPacks filter { isPrefixOf(_,fullNameList) } maxBy(_.length)
        (pack, fullNameList drop pack.length)
      }} getOrElse {
        // No package matches
        (Nil, fullNameList)
      }
      
      assert(!objectPart.isEmpty)     
      
      val point = program.modules find { mod => 
        mod.id.toString == objectPart.head && 
        inPackage(mod)  == packagePart
      } orElse {
        onCondition (exploreStandalones) {
          // Search in standalone objects
          program.modules.collect {
            case ModuleDef(_,subDefs,true) => subDefs 
          }.flatten.find { df =>
            df.id.toString == objectPart.head && 
            inPackage(df)  == packagePart 
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
  
  
  
  import Trees.Expr
  import TreeOps.{preMap, postMap}
  
  /*
   * Apply an expression operation on all expressions contained in a FunDef
   */
  def applyOnFunDef(operation : Expr => Expr)(funDef : FunDef): FunDef = {
    val newFunDef = funDef.duplicate 
    newFunDef.body          = funDef.body           map operation
    newFunDef.precondition  = funDef.precondition   map operation
    newFunDef.postcondition = funDef.postcondition  map { case (id, ex) => (id, operation(ex))}
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
  

}
