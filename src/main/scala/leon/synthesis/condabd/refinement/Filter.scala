package leon.synthesis
package condabd.refinement

import scala.collection.mutable.{Seq => _, _}

import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Definitions._
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps

import condabd.insynth.leon.loader.LeonLoader
import insynth.util.logging.HasLogger

/**
 * Class used for filtering out unnecessary candidates during the search
 */
class Filter(program: Program, holeFunDef: FunDef, refiner: VariableRefiner) extends HasLogger {      
    
  // caching of previously filtered expressions
  type FilterSet = HashSet[Expr]
  private var seenBranchExpressions: FilterSet = new FilterSet()
  
  /**
   * expr - expression to check
   * funDefArgs - list of identifiers according to which well ordering is checked
   */
  def isAvoidable(expr: Expr, funDefArgs: List[Identifier]) = {
    finest(
      "Results for refining " + expr + ", are: " +
      " ,isCallAvoidableBySize(expr) " + isCallAvoidableBySize(expr, funDefArgs) +
      " ,hasDoubleRecursion(expr) " + hasDoubleRecursion(expr) +
      " ,isOperatorAvoidable(expr) " + isOperatorAvoidable(expr) +
      " ,isUnecessaryInstanceOf(expr) " + isUnecessaryInstanceOf(expr) +
  		", isUnecessaryStructuring(expr) " + isUnecessaryStructuring(expr)
    )
    if (seenBranchExpressions contains expr) {
      true
    } else {
	    val result = isCallAvoidableBySize(expr, funDefArgs) || hasDoubleRecursion(expr) ||
  									isOperatorAvoidable(expr) || isUnecessaryInstanceOf(expr) ||
  									isUnecessaryStructuring(expr)
  									
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
    TreeOps.exists(isBadInvocation)(expr)
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
    def recursionLevel(expr: Expr, rec: Seq[Int]) = expr match {
      case FunctionInvocation(`holeFunDef`, args) => (0 +: rec).max + 1
      case _ =>  (0 +: rec).max
    }

    TreeOps.foldRight(recursionLevel)(expr) >= 2
  }
  
  // removing checking instance of fields (e.g. x.field.isInstanceOf[..]) - this is deemed unecessary
  def isUnecessaryStructuring(expr: Expr) = {
    var found = false
    
    def isCaseClassSelector(expr: Expr) = expr match {    
	    case CaseClassInstanceOf(_, _: CaseClassSelector) =>
	    	found = true
	    	None
	    case _ => None
    }
    
    TreeOps.postMap(isCaseClassSelector)(expr)
    
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
  
  def isUnecessaryInstanceOf(expr: Expr) = expr match {
    // if we check instance of an constructor we know that it is a constant
//      case CaseClassInstanceOf(_, _: CaseClass) =>
//        true
    case CaseClassInstanceOf(cct, _: FunctionInvocation) =>
      true
    case CaseClassInstanceOf(cct, innerExpr)
      if innerExpr.getType == cct =>
      true
    case CaseClassInstanceOf(cct, v @ Variable(id)) => {
      val possibleTypes = refiner.getPossibleTypes(id)
      if (possibleTypes.size == 1)
        possibleTypes.head.classDef == cct.classDef
      else
        false
    }
    case _ => false
  }
}
