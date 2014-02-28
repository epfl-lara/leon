/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

import z3.scala._

import leon.solvers._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._

/** This is a rather direct mapping to Z3, where all functions are left uninterpreted.
 *  It reports the results as follows (based on the negation of the formula):
 *    - if Z3 reports UNSAT, it reports VALID
 *    - if Z3 reports SAT and the formula contained no function invocation, it returns INVALID with the counter-example/model
 *    - otherwise it returns UNKNOWN
 *  Results should come back very quickly.
 */
class UIFZ3Solver(val context : LeonContext, val program: Program,     
    useBitvectors : Boolean = false,
    bitvecSize: Int = 32,
    autoComplete : Boolean = true)
  extends AbstractZ3Solver
     with Z3ModelReconstruction {
  
  val name = "Z3-u"
  val description = "Uninterpreted Z3 Solver"
  override val AUTOCOMPLETEMODELS : Boolean = autoComplete  

  // this is fixed
  protected[leon] val z3cfg = new Z3Config(
    "MODEL" -> true,
    "UNSAT_CORE" -> true,
    //"NLSAT" -> true,
    //"MBQI" -> false,
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

  initZ3

  val solver = z3.mkSolver

  def push() {
    solver.push
  }


  def pop(lvl: Int = 1) {
    solver.pop(lvl)    
  }

  private var variables = Set[Identifier]()

  def assertCnstr(expression: Expr) {
    variables ++= variablesOf(expression)
    
    if(useBitvectors){
      val bform = toBitVectorFormula(expression, bitvecSize).get     
      solver.assertCnstr(bform)
    } 
    else {
      solver.assertCnstr(toZ3Formula(expression).get)
    }    
  }

  def innerCheck: Option[Boolean] = {
    solver.check
  }

  def innerCheckAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    variables ++= assumptions.flatMap(variablesOf(_))
    
    if(useBitvectors){
      solver.checkAssumptions(assumptions.toSeq.map(toBitVectorFormula(_, bitvecSize).get) : _*)
    } else {
      solver.checkAssumptions(assumptions.toSeq.map(toZ3Formula(_).get) : _*)  
    }
  }

  def getModel = {
    modelToMap(solver.getModel, variables)
  }
  
  def compeleteModel(ids : Seq[Identifier]) : Unit = {
    for (id <- ids) {
      solver.getModel.eval(exprToZ3Id(id.toVariable), true)
    }
  }

  def getUnsatCore = {
    solver.getUnsatCore.map(ast => fromZ3Formula(null, ast, None) match {
      case n @ Not(Variable(_)) => n
      case v @ Variable(_) => v
      case x => scala.sys.error("Impossible element extracted from core: " + ast + " (as Leon tree : " + x + ")")
    }).toSet
  }

  def evalExpr(expr: Expr): Option[Expr] = {    
    val ast = if(useBitvectors) {
      toBitVectorFormula(expr, bitvecSize).get
    } else {
      toZ3Formula(expr).get
    }
    //println("Evaluating: "+ast+" using: "+solver.getModel+" Result: "+solver.getModel.eval(ast, true))
    val model = solver.getModel
    val res = model.eval(ast, true)
    if (res.isDefined)
      Some(fromZ3Formula(model, res.get, Some(expr.getType)))
    else None
  }

  /**
   * Evaluates the given boolean expression using the model
   */
  def evalBoolExpr(expr: Expr): Option[Boolean] = {
    val ast = if (useBitvectors) {
      toBitVectorFormula(expr, bitvecSize).get
    } else {
      toZ3Formula(expr).get
    }
    //println("Evaluating: "+ast+" using: "+solver.getModel+" Result: "+solver.getModel.eval(ast, true))
    val model = solver.getModel
    val res = model.eval(ast, true)
    model.context.getBoolValue(res.get)
  }
  
  def ctrsToString(logic : String, pruneDefs : Boolean = true) : String = {        
    z3.setAstPrintMode(Z3Context.AstPrintMode.Z3_PRINT_SMTLIB2_COMPLIANT)    
    var i = 0
    var smtstr = solver.getAssertions().toSeq.foldLeft("")((acc, asser) => {      
      val str = z3.benchmarkToSMTLIBString("benchmark", logic, "unknown", "", Seq(), asser)

      val newstr = if (i > 0) {
        //remove from the string the headers and also redeclaration of template variables
        //split based on newline to get a list of strings
        val strs = str.split("\n")
        val newstrs =
          strs.filter((line) => {
            if (line == "; benchmark") false
            else if (line.startsWith("(set")) false
            else {
              if (pruneDefs) {
                if (line.startsWith("(declare-fun")) {
                  val fields = line.split(" ")
                  if (!fields(1).startsWith("l"))
                    false
                  else true
                } else true
              } else true
            }
          })                
        newstrs.foldLeft("")((acc, line) => acc + "\n" + line)
      } else str
      
      i += 1
      acc + newstr
    })
    
    //finally add a get-model query
    smtstr +=  "(get-model)"
    smtstr
  } 
}
