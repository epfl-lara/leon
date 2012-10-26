package leon
package solvers.z3

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import Extensions._

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
class UninterpretedZ3Solver(reporter : Reporter) extends Solver(reporter) with AbstractZ3Solver with Z3ModelReconstruction {
  val description = "Uninterpreted Z3 Solver"
  override val shortDescription = "Z3-u"

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "MBQI" -> false,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
  )
  toggleWarningMessages(true)

  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty
  protected[leon] def prepareFunctions : Unit = {
    functionMap        = Map.empty
    reverseFunctionMap = Map.empty
    for(funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
    }
  }
  protected[leon] def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = functionMap(funDef)
  protected[leon] def functionDeclToDef(decl: Z3FuncDecl) : FunDef = reverseFunctionMap(decl)
  protected[leon] def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)

  override def solve(expression: Expr) : Option[Boolean] = solveOrGetCounterexample(expression)._1

  // Where the solving occurs
  override def solveOrGetCounterexample(expression : Expr) : (Option[Boolean],Map[Identifier,Expr]) = {
    val emptyModel    = Map.empty[Identifier,Expr]
    val unknownResult = (None, emptyModel)
    val validResult   = (Some(true), emptyModel)

    containedInvocations = false
    val result = toZ3Formula(expression).map { asZ3 => 
      z3.assertCnstr(z3.mkNot(asZ3))
      z3.checkAndGetModel() match {
        case (Some(false), _) => validResult
        case (Some(true), model) if !containedInvocations => {
          val variables = variablesOf(expression)
          val r = (Some(false), modelToMap(model, variables))
          model.delete
          r
        }
        case _ => unknownResult
      }
    } getOrElse unknownResult

    result
  }

  private var containedInvocations : Boolean = _

  override def toZ3Formula(expr : Expr, m : Map[Identifier,Z3AST] = Map.empty) : Option[Z3AST] = {
    expr match {
      case FunctionInvocation(_, _) => containedInvocations = true
      case _ => ;
    }
    super.toZ3Formula(expr,m)
  }
}
