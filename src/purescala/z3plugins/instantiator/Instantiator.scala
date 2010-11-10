package purescala.z3plugins.instantiator

import z3.scala._

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._

import purescala.Z3Solver

class Instantiator(val z3Solver: Z3Solver) extends Z3Theory(z3Solver.z3, "Instantiator") {
  import z3Solver.{z3,program,typeToSort}

  setCallbacks(
    reduceApp = true,
//    finalCheck = true,
//    push = true,
//    pop = true,
    newApp = true,
    newAssignment = true,
    newRelevant = true,
//    newEq = true,
//    newDiseq = true,
//    reset = true,
    restart = true
  )

  showCallbacks(true)

  private var functionMap : Map[FunDef,Z3FuncDecl] = Map.empty

  protected[purescala] def registerFunction(funDef: FunDef, sorts: Seq[Z3Sort], returnSort: Z3Sort) : Unit = {
    functionMap = functionMap + (funDef -> mkTheoryFuncDecl(z3.mkStringSymbol(funDef.id.uniqueName), sorts, returnSort)) 
  }

  def functionDefToDef(funDef: FunDef) : Z3FuncDecl = {
    functionMap.getOrElse(funDef, scala.Predef.error("No Z3 definition found for function symbol "+ funDef.id.name + " in Instantiator."))
  }

  override def newAssignment(ast: Z3AST, polarity: Boolean) : Unit = {

  }

  override def newApp(ast: Z3AST) : Unit = {

  }

  override def newRelevant(ast: Z3AST) : Unit = {

  }

  override def restart : Unit = { }
}
