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
