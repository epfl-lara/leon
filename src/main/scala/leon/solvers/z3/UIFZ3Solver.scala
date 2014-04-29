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
import leon.invariant.factories.TemplateIdFactory

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
    autoComplete : Boolean = true,
    handleOverflows: Boolean = false)
  extends AbstractZ3Solver
     with Z3ModelReconstruction {
  
  val name = "Z3-u"
  val description = "Uninterpreted Z3 Solver"
  val AUTOCOMPLETEMODELS : Boolean = autoComplete  

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

/*  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty
  protected[leon] def prepareFunctions : Unit = {
    functionMap        = Map.empty
    reverseFunctionMap = Map.empty
    for(funDef <- program.definedFunctions) {
      val sortSeq = funDef.params.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
    }
  }
  protected[leon] def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = functionMap(funDef)
  protected[leon] def functionDeclToDef(decl: Z3FuncDecl) : FunDef = reverseFunctionMap(decl)
  protected[leon] def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)*/

  initZ3

  val solver = z3.mkSolver

  def push() {
    solver.push
  }


  def pop(lvl: Int = 1) {
    solver.pop(lvl)    
  }

  private var freeVariables = Set[Identifier]()

  def assertCnstr(expression: Expr) {
    freeVariables ++= variablesOf(expression)
    
    if(useBitvectors){
      val bform = toBitVectorFormula(expression, bitvecSize).get     
      solver.assertCnstr(bform)
    } 
    else {
      solver.assertCnstr(toZ3Formula(expression).get)
    }    
  }

  override def check: Option[Boolean] = {
    solver.check
  }    

  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    freeVariables ++= assumptions.flatMap(variablesOf(_))
    
    if(useBitvectors){
      solver.checkAssumptions(assumptions.toSeq.map(toBitVectorFormula(_, bitvecSize).get) : _*)
    } else {
      solver.checkAssumptions(assumptions.toSeq.map(toZ3Formula(_).get) : _*)  
    }
  }
  
  def getAssertions : Expr = {
    val assers = solver.getAssertions.map((ast) => fromZ3Formula(null, ast))
    And(assers)
  }

  def getModel = {
    if(handleOverflows) 
      getModelWithoutOverflows
    else  
      modelToMap(solver.getModel, freeVariables)    
  }
  
  /**
   * This getmodel method tries to handle overflows
   */
  class OverflowException(msg: String) extends Exception(msg)

  def getModelWithoutOverflows: Map[Identifier, Expr] = {

    def rangeExpr(id: Identifier): Expr = {
      val (minv, maxv) = if (id.getType == Int32Type) {
        (IntLiteral(minNumeralVal), IntLiteral(maxNumeralVal))
      } else if (id.getType == RealType) {
        (RealLiteral(minNumeralVal, 1), RealLiteral(maxNumeralVal, 1))
      } else
        throw IllegalStateException("Unexpected Type: " + id.getType)
      val idvar = id.toVariable
      And(GreaterEquals(idvar, minv), LessEquals(idvar, maxv))
    }

    val model = modelToMap(solver.getModel, freeVariables)
    //TODO: should we recurse into tuples to discover a overflow ??
    val newbounds = model.collect {
      case (id, il @ IntLiteral(_)) if il.hasOverflow => rangeExpr(id)
      case (id, rl @ RealLiteral(_, _)) if (rl.hasOverflow && TemplateIdFactory.IsTemplateIdentifier(id)) => {
        val Some((bignum, bigdem)) = rl.getBigRealValue
        val floor = (bignum / bigdem)
        if (this.containedInRange(floor)) {
          //here, use some heuristics to converge to a smaller numerator and denominator
          println("Large fractions found..."+id+"=("+bignum +"/"+bigdem+")"+" searching for smaller ones...")
          val intv = floor.intValue
          val boundExpr = if(intv < 0) GreaterEquals(id.toVariable, RealLiteral(intv, 1)) 
          				  else LessEquals(id.toVariable, RealLiteral(intv, 1))
          boundExpr
        } else
          rangeExpr(id)
      }
    }.toSeq

    if (newbounds.isEmpty)
      model
    else {
      solver.push
      solver.assertCnstr(toZ3Formula(And(newbounds)).get)
      solver.check match {
        case Some(true) =>
          val newmodel = getModelWithoutOverflows
          solver.pop()
          newmodel
        case _ => throw new OverflowException("Cannot handle overflows!")
      }
    }
  }
  
  def compeleteModel(ids : Seq[Identifier]) : Unit = {
    for (id <- ids) {
      solver.getModel.eval(variables.leonToZ3(id.toVariable), true)
    }
  }

  def getUnsatCore = {
    solver.getUnsatCore.map(ast => fromZ3Formula(null, ast) match {
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
      Some(fromZ3Formula(model, res.get))
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

  def ctrsToString(logic: String, unsatcore: Boolean = false): String = {
    z3.setAstPrintMode(Z3Context.AstPrintMode.Z3_PRINT_SMTLIB2_COMPLIANT)
    var seenHeaders = Set[String]()
    var headers = Seq[String]()
    var asserts = Seq[String]()
    solver.getAssertions().toSeq.foreach((asser) => {
      val str = z3.benchmarkToSMTLIBString("benchmark", logic, "unknown", "", Seq(), asser)
      //println("str: "+ str)
      //remove from the string the headers and also redeclaration of template variables
      //split based on newline to get a list of strings
      val strs = str.split("\n")
      val newstrs = strs.filter((line) => !seenHeaders.contains(line))
      var newHeaders = Seq[String]()
      newstrs.foreach((line) => {
        if (line == "; benchmark") newHeaders :+= line
        else if (line.startsWith("(set")) newHeaders :+= line
        else if (line.startsWith("(declare")) newHeaders :+= line
        else if(line.startsWith("(check-sat)")) {} //do nothing        
        else asserts :+= line
      })
      headers ++= newHeaders
      seenHeaders ++= newHeaders
      //newstrs.foldLeft("")((acc, line) => acc + "\n" + line)      
    })
    val initstr = if (unsatcore) {
      "(set-option :produce-unsat-cores true)"
    } else ""
    val smtstr = headers.foldLeft(initstr)((acc, hdr) => acc + "\n" + hdr) + "\n" +
      asserts.foldLeft("")((acc, asrt) => acc + "\n" + asrt) + "\n" +
      "(check-sat)" + "\n" +
      (if (!unsatcore) "(get-model)"
      else "(get-unsat-core)")
    smtstr
  } 
}
