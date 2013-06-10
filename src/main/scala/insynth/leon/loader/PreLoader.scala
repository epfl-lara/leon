package insynth.leon.loader

import insynth.structures.{ SuccinctType => InSynthType }
import insynth.leon.{ LeonDeclaration => Declaration, NaryReconstructionExpression => NAE, ImmediateExpression => IE }
import insynth.engine.InitialEnvironmentBuilder

import leon.purescala.Definitions.{ Program, FunDef }
import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Common.{ Identifier }
import leon.purescala.Trees._

object PreLoader extends ( (Boolean) => List[Declaration] ) {
  
  import DeclarationFactory._
  
  def apply(loadArithmeticOps: Boolean = true): List[Declaration] = {

    val supportedBaseTypes = List(BooleanType, Int32Type)
    var list = scala.collection.mutable.MutableList[Declaration]()
        
    list += getAnd
    list += getNot
    
    list += getLessEquals
    list += getLessThan
    list += getGreaterThan
    list ++= getEquals(supportedBaseTypes)
    
    if (loadArithmeticOps)
      list ++= getArithmeticOps
    
    list toList
  }
  
  def getAnd =
    // case And(args) if args.isEmpty => BooleanLiteral(true)    
    makeDeclaration(
      makeNAE("And", { case List(arg1, arg2) => And( List(arg1, arg2) ) }),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    )    
    
  def getNot =
    // case Not(arg) => rec(ctx, arg) match {
    makeDeclaration(
      makeNAE( "Not", { case List(arg) => Not( arg ) } ),
      FunctionType( List(BooleanType), BooleanType )
    )
    
  def getOr =
    // case Or(args) if args.isEmpty => BooleanLiteral(false)    
    makeDeclaration(
      makeNAE( "Or", { case List(arg1, arg2) => Or( List(arg1, arg2) ) } ),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    )  
    
  def getImplies =
    // case Implies(l, r) => (rec(ctx, l), rec(ctx, r)) match {
    makeDeclaration(
      makeNAE( "=>", { case List(left, right) => Implies( left, right ) } ),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    ) 
    
  def getIff =
    //case Iff(le, re) => (rec(ctx, le), rec(ctx, re)) match {
    makeDeclaration(
      makeNAE( "<=>", { case List(left, right) => Iff( left, right ) } ),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    ) 
    
  def getEquals(listOfInstanceTypes: List[LeonType]) =
    // case Equals(le, re) => {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "=", { case List(left, right) => Equals( left, right ) } ),
	      FunctionType( List(x, x), BooleanType ),
	      true
	    ) 
    }
    
  def getArithmeticOps = {
	    // case Plus(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "+", { case List(left, right) => Plus( left, right ) } ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case Minus(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "-", { case List(left, right) => Minus( left, right ) } ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case UMinus(e) => rec(ctx, e) match {
	    makeDeclaration(
	      makeNAE( "UMinus", { case List(e) => UMinus( e ) } ),
	      FunctionType( List(Int32Type), Int32Type )
	    ) ::
	  	//case Times(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "*", { case List(left, right) => Times( left, right ) } ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case Division(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "/", { case List(left, right) => Division( left, right ) } ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case Modulo(l,r) => (rec(ctx,l), rec(ctx,r)) match {
	    makeDeclaration(
	      makeNAE( "%", { case List(left, right) => Modulo( left, right ) } ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) :: Nil
    }
    
  def getLessThan =
    // case LessThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( "<", { case List(left, right) => LessThan( left, right ) } ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 
    
  def getGreaterThan =
    // case GreaterThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( ">", { case List(left, right) => GreaterThan( left, right ) } ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 
    
  def getLessEquals =
    // case LessEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( "<=", { case List(left, right) => LessEquals( left, right ) } ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 
    
  def getGreaterEquals =
    // case GreaterEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( ">=", { case List(left, right) => GreaterEquals( left, right ) } ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 

  // currently Leon has some troubles with sets    
  def getSetOperations(listOfInstanceTypes: List[LeonType]) = {
        
    // case SetUnion(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetUnion", { case List(left, right) => SetUnion( left, right ) } ),
	      FunctionType( List(SetType(x), SetType(x)), SetType(x) )
	    )       
    } ++
    //case SetIntersection(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetIntersection", { case List(left, right) => SetIntersection( left, right ) } ),
	      FunctionType( List(SetType(x), SetType(x)), SetType(x) )
	    )       
    } ++
    //case SetDifference(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetDifference", { case List(left, right) => SetDifference( left, right ) } ),
	      FunctionType( List(SetType(x), SetType(x)), SetType(x) )
	    )       
    } ++
    //case ElementOfSet(el,s) => (rec(ctx,el), rec(ctx,s)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "ElementOfSet", { case List(left, right) => ElementOfSet( left, right ) } ),
	      FunctionType( List(x, SetType(x)), BooleanType )
	    )       
    } ++
    // case SetCardinality(s) => {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetCardinality", { case List(set) => SetCardinality( set ) } ),
	      FunctionType( List(SetType(x)), Int32Type )
	    )       
    }
    
  }
    
    // not covered atm
//    case CaseClass(cd, args) => CaseClass(cd, args.map(rec(ctx, _)))
//    case CaseClassInstanceOf(cd, expr) => {
//    case CaseClassSelector(cd, expr, sel) => {
  
    // we do not synthesize ifs explicitly
  	//case IfExpr(cond, then, elze) => {
  def getIfExpr(listOfInstanceTypes: List[LeonType]) = {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "If", { case List(cond: Expr, then: Expr, elze: Expr) => IfExpr(cond, then, elze) } ),
	      FunctionType( List(BooleanType, x, x), x )
	    )       
    }
  }
    
//    no arrays atm
//    case f @ ArrayFill(length, default) => {
//    case ArrayLength(a) => 
//    case ArrayUpdated(a, i, v) => 
//    case ArraySelect(a, i) => 
//    case FiniteArray(exprs) => 

    // no maps atm
//    case g @ MapGet(m,k) => (rec(ctx,m), rec(ctx,k)) match {
//    case u @ MapUnion(m1,m2) => (rec(ctx,m1), rec(ctx,m2)) match {
//    case i @ MapIsDefinedAt(m,k) => (rec(ctx,m), rec(ctx,k)) match {
      
    // needed?
//    case Distinct(args) => {
    
    // not covered atm      
    // case Tuple(ts) => {
    // case TupleSelect(t, i) => {
		// should produce all declarations with tupleselect
    
    // needed?
    //case Waypoint(_, arg) => rec(ctx, arg)
    //case FunctionInvocation(fd, args) => {
  
  def getLiteralDeclarations = {
    
    var list = scala.collection.mutable.MutableList[Declaration]()
    
//    case i @ IntLiteral(_) => i
    list += makeLiteral(
      IE( "IntLit", IntLiteral(0) ),
      Int32Type
    ) 
//    case b @ BooleanLiteral(_) => b
    list += makeLiteral(
      IE( "BoolLit", BooleanLiteral(false) ),
      BooleanType
    ) 
//    case u @ UnitLiteral => u
    list += makeLiteral(
      IE( "UnitLit", UnitLiteral ),
      UnitType
    ) 
    
//    case e @ EmptySet(_) => e
    // NOTE sets are removed in Leon
//    yieldDeclarationForTypes(listOfInstanceTypes) {
//      x: LeonType =>
//	    list += makeDeclaration(
//	      IE( "SetLit", EmptySet(x) ),
//	      SetType(x)
//	    )       
//    }
    
    list toList
  }
    
  def makeNAE( name: String, fun: List[Expr]=>Expr ): NAE = NAE( name, fun )  

}