package lesynth
package refinement

import scala.collection.mutable._

import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Definitions._
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps
import leon.plugin.ExtractionPhase

import insynth.leon.loader.LeonLoader
import insynth.util.logging.HasLogger

class Filter(program: Program, holeFunDef: FunDef, refiner: VariableRefiner) extends HasLogger {      
  
  // caching of previously filtered expressions
  type FilterSet = HashSet[Expr]
  private var seenBranchExpressions: FilterSet = new FilterSet()
  
  def isAvoidable(expr: Expr, funDefArgs: List[Identifier]) = {
    finest(
      "Results for refining " + expr + ", are: " +
      " ,isCallAvoidableBySize(expr) " + isCallAvoidableBySize(expr, funDefArgs) +
      " ,hasDoubleRecursion(expr) " + hasDoubleRecursion(expr) +
      " ,isOperatorAvoidable(expr) " + isOperatorAvoidable(expr) +
      " ,isUnecessaryInstanceOf(expr) " + isUnecessaryInstanceOf(expr)
    )
    if (seenBranchExpressions contains expr) {
      true
    } else {
	    val result = isCallAvoidableBySize(expr, funDefArgs) || hasDoubleRecursion(expr) ||
  									isOperatorAvoidable(expr) || isUnecessaryInstanceOf(expr)
  									
			// cache results
			if (result) {
			  seenBranchExpressions += expr			  
			}
		  result
    }
  }
    
  val pureRecurentExpression: Expr = 
	  if (holeFunDef.hasBody) {
	    FunctionInvocation(holeFunDef, holeFunDef.args map { _.toVariable })
	  } else
	    Error("Hole FunDef should have a body")
  fine("Refiner initialized. Recursive call: " + pureRecurentExpression)
    
  def isBadInvocation(expr2: Expr) = expr2 match {
    case `pureRecurentExpression` =>
      fine("Pure recurrent expression detected: " + pureRecurentExpression)
      true
    case FunctionInvocation(`holeFunDef`, args) =>
      (0 /: (args zip holeFunDef.args.map(_.id))) {
        case (res, (arg, par)) if res == 0 => isLess(arg, par)
        case (res, _) => res
      } >= 0
    case _ => false
  }
  
  // check according to size
  // true - YES, false - NO or don't know
  // basically a lexicographic (well-founded) ordering
  def isCallAvoidableBySize(expr: Expr, funDefArgs: List[Identifier]) = {
	    		    
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
//	      finest("Refiner: Variable IDs do not match: " + v.id.uniqueName + " and " + variable.uniqueName )
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
  
  def isUnecessaryInstanceOf(expr: Expr) = {
    def isOfClassType(exp: Expr, classDef: ClassTypeDef) =
      expr.getType match {
        case tpe: ClassType => tpe.classDef == classDef
        case _ => false
      }
    expr match {
	    case CaseClassInstanceOf(classDef, innerExpr)
	    	if isOfClassType(innerExpr, classDef) =>
	      true
	    case CaseClassInstanceOf(classDef, v@Variable(id)) => {
	      val possibleTypes = refiner.getPossibleTypes(id)
	      if (possibleTypes.size == 1)
	        possibleTypes.head.classDef == classDef
	      else
	        false
	    }
	    case _ => false
    }
  }
  
}