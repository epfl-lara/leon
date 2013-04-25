package lesynth

import leon.purescala.Trees._
import leon.purescala.Definitions.{ Program, VarDecl, FunDef, VarDecls }
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps
import leon.plugin.ExtractionPhase

import insynth.leon.loader.LeonLoader

import insynth.util.logging.HasLogger

class Refiner(program: Program, hole: Hole, holeFunDef: FunDef) extends HasLogger {      
  import Globals._
  
  def isAvoidable(expr: Expr, funDefArgs: List[Identifier]) = {
    fine(
      "Results for refining " + expr + ", are: " +
      " ,recurentExpression == expr " + (recurentExpression == expr) +
      " ,isCallAvoidableBySize(expr) " + isCallAvoidableBySize(expr, funDefArgs) +
      " ,hasDoubleRecursion(expr) " + hasDoubleRecursion(expr) +
      " ,isOperatorAvoidable(expr) " + isOperatorAvoidable(expr)
    )
    recurentExpression == expr || isCallAvoidableBySize(expr, funDefArgs) || hasDoubleRecursion(expr) || isOperatorAvoidable(expr)
  }
  
  //val holeFunDef = Globals.holeFunDef
    
  val recurentExpression: Expr = 
	  if (holeFunDef.hasBody) {
	    FunctionInvocation(holeFunDef, holeFunDef.args map { varDecl => Variable(varDecl.id) })
	  } else
	    Error("Hole FunDef should have a body")
    
  // check according to size
  // true - YES, false - NO or don't know
  // basically a lexicographic (well-founded) ordering
  def isCallAvoidableBySize(expr: Expr, funDefArgs: List[Identifier]) = {
	    	
    def isBadInvocation(expr2: Expr) = expr2 match {
	    case FunctionInvocation(`holeFunDef`, args) =>
	      (0 /: (args zip holeFunDef.args.map(_.id))) {
	        case (res, (arg, par)) if res == 0 => isLess(arg, par)
	        case (res, _) => res
	      } >= 0
	    case _ => false
	  }
	    
  	import TreeOps.treeCatamorphism
  	
  	treeCatamorphism(
	    isBadInvocation,
	    (b1: Boolean, b2: Boolean) => b1 || b2,
	    (t: Expr, b: Boolean) => b || isBadInvocation(t),
	    expr
    )  
  }
  
  def isLess(arg: Expr, variable: Identifier): Int = {
	  def getSize(arg: Expr, size: Int): Int = arg match {
    	//case FunctionInvocation(_, args) => -1 // if some random calls are involved
	    case CaseClassSelector(cas, expr, fieldId) if fieldId.name == "tail" => getSize(expr, size - 1)
	    case CaseClassSelector(cas, expr, fieldId) if fieldId.name == "head" => size + 1
	    case CaseClass(caseClassDef, head :: tail :: Nil) => getSize(tail, size + 1)
	    case CaseClass(caseClassDef, Nil) => 1
	    case v: Variable => if (v.id == variable) size else {
	      fine("variable IDs do not match: " + v.id.uniqueName + " and " + variable.uniqueName )
	      1
	    }
	    case _ => //throw new RuntimeException("Could not match " + arg + " in getSize")
	      -1
	  }
	  
	  getSize(arg, 0)
  }
  
  def hasDoubleRecursion(expr: Expr) = {      
    var found = false
    
  	def findRecursion(expr: Expr) = expr match {
	    case FunctionInvocation(`holeFunDef`, args) => true
	    case _ => false
	  }
    
  	def findRecursionInCall(expr: Expr, b: Boolean) = expr match {
	    case FunctionInvocation(`holeFunDef`, args) =>
	      if (b) found = true
	      true
	    case _ => b
	  }
  	
  	import TreeOps.treeCatamorphism
  	
  	treeCatamorphism(findRecursion, (b1: Boolean, b2: Boolean) => b1 || b2, findRecursionInCall, expr)
  	
  	found
  }
  
  def isOperatorAvoidable(expr: Expr) = expr match {
    case And(expr1 :: expr2) if expr1 == expr2 => true 
    case Or(expr1 :: expr2) if expr1 == expr2 => true 
    case LessThan(expr1, expr2) if expr1 == expr2 => true 
    case LessEquals(expr1, expr2) if expr1 == expr2 => true 
    case GreaterThan(expr1, expr2) if expr1 == expr2 => true 
    case GreaterEquals(expr1, expr2) if expr1 == expr2 => true 
    case Equals(expr1, expr2) if expr1 == expr2 => true 
    case _ => false
  }
  
}