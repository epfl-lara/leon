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
      makeNAE("And", (args: List[Expr]) => And( args )),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    )
    
  def getNot =
    // case Not(arg) => rec(ctx, arg) match {
    makeDeclaration(
      makeNAE( "Not", (args: List[Expr]) => Not( args.head ) ),
      FunctionType( List(BooleanType), BooleanType )
    )
    
  def getOr =
    // case Or(args) if args.isEmpty => BooleanLiteral(false)    
    makeDeclaration(
      makeNAE( "Or", (args: List[Expr]) => Or( args ) ),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    )  
    
  def getImplies =
    // case Implies(l, r) => (rec(ctx, l), rec(ctx, r)) match {
    makeDeclaration(
      makeNAE( "=>", (args: List[Expr]) => Implies( args(0), args(1) ) ),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    ) 
    
  def getIff =
    //case Iff(le, re) => (rec(ctx, le), rec(ctx, re)) match {
    makeDeclaration(
      makeNAE( "<=>", (args: List[Expr]) => Iff( args(0), args(1) ) ),
      FunctionType( List(BooleanType, BooleanType), BooleanType )
    ) 
    
  def getEquals(listOfInstanceTypes: List[LeonType]) =
    // case Equals(le, re) => {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "=", (args: List[Expr]) => Equals( args(0), args(1) ) ),
	      FunctionType( List(x, x), BooleanType ),
	      true
	    ) 
    }
    
  def getArithmeticOps = {
	    // case Plus(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "+", (args: List[Expr]) => Plus( args(0), args(1) ) ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case Minus(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "-", (args: List[Expr]) => Minus( args(0), args(1) ) ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case UMinus(e) => rec(ctx, e) match {
	    makeDeclaration(
	      makeNAE( "UMinus", (args: List[Expr]) => UMinus( args.head ) ),
	      FunctionType( List(Int32Type), Int32Type )
	    ) ::
	  	//case Times(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "*", (args: List[Expr]) => Times( args(0), args(1) ) ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case Division(l, r) => (rec(ctx, l), rec(ctx, r)) match {
	    makeDeclaration(
	      makeNAE( "/", (args: List[Expr]) => Division( args(0), args(1) ) ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) ::
	    // case Modulo(l,r) => (rec(ctx,l), rec(ctx,r)) match {
	    makeDeclaration(
	      makeNAE( "%", (args: List[Expr]) => Modulo( args(0), args(1) ) ),
	      FunctionType( List(Int32Type, Int32Type), Int32Type )
	    ) :: Nil
    }
    
  def getLessThan =
    // case LessThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( "<", (args: List[Expr]) => LessThan( args(0), args(1) ) ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 
    
  def getGreaterThan =
    // case GreaterThan(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( ">", (args: List[Expr]) => GreaterThan( args(0), args(1) ) ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 
    
  def getLessEquals =
    // case LessEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( "<=", (args: List[Expr]) => LessEquals( args(0), args(1) ) ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 
    
  def getGreaterEquals =
    // case GreaterEquals(l,r) => (rec(ctx,l), rec(ctx,r)) match {
    makeDeclaration(
      makeNAE( ">=", (args: List[Expr]) => GreaterEquals( args(0), args(1) ) ),
      FunctionType( List(Int32Type, Int32Type), BooleanType )
    ) 

  // currently Leon has some troubles with sets    
  def getSetOperations(listOfInstanceTypes: List[LeonType]) = {
        
    // case SetUnion(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetUnion", (args: List[Expr]) => SetUnion( args(0), args(1) ) ),
	      FunctionType( List(SetType(x), SetType(x)), SetType(x) )
	    )       
    } ++
    //case SetIntersection(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetIntersection", (args: List[Expr]) => SetIntersection( args(0), args(1) ) ),
	      FunctionType( List(SetType(x), SetType(x)), SetType(x) )
	    )       
    } ++
    //case SetDifference(s1,s2) => (rec(ctx,s1), rec(ctx,s2)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetDifference", (args: List[Expr]) => SetDifference( args(0), args(1) ) ),
	      FunctionType( List(SetType(x), SetType(x)), SetType(x) )
	    )       
    } ++
    //case ElementOfSet(el,s) => (rec(ctx,el), rec(ctx,s)) match {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "ElementOfSet", (args: List[Expr]) => ElementOfSet( args(0), args(1) ) ),
	      FunctionType( List(x, SetType(x)), BooleanType )
	    )       
    } ++
    // case SetCardinality(s) => {
    yieldDeclarationForTypes(listOfInstanceTypes) {
      x: LeonType =>
	    makeDeclaration(
	      makeNAE( "SetCardinality", (args: List[Expr]) => SetCardinality( args(0) ) ),
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
	      makeNAE( "If", (args: List[Expr]) => args match {
	        case List(cond, then, elze) => IfExpr(cond, then, elze)
	        case _ => throw new RuntimeException
	      }),
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