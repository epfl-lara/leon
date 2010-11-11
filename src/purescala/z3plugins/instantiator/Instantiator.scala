package purescala.z3plugins.instantiator

import z3.scala._

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._

import purescala.Z3Solver

class Instantiator(val z3Solver: Z3Solver) extends Z3Theory(z3Solver.z3, "Instantiator") {
  import z3Solver.{z3,program,typeToSort,fromZ3Formula,toZ3Formula}

  setCallbacks(
//    reduceApp = true,
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
  private var reverseFunctionMap : Map[Z3FuncDecl,FunDef] = Map.empty

  protected[purescala] def registerFunction(funDef: FunDef, sorts: Seq[Z3Sort], returnSort: Z3Sort) : Unit = {
    val z3Decl = mkTheoryFuncDecl(z3.mkStringSymbol(funDef.id.uniqueName), sorts, returnSort) 
    functionMap = functionMap + (funDef -> z3Decl)
    reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
  }

  def isKnownDef(funDef: FunDef) : Boolean = functionMap.isDefinedAt(funDef)
  def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = {
    functionMap.getOrElse(funDef, scala.Predef.error("No Z3 definition found for function symbol "+ funDef.id.name + " in Instantiator."))
  }
  def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)
  def functionDeclToDef(decl: Z3FuncDecl) : FunDef = {
    reverseFunctionMap.getOrElse(decl, scala.Predef.error("No FunDef found for Z3 definition " + decl + " in Instantiator."))
  }

  override def newAssignment(ast: Z3AST, polarity: Boolean) : Unit = {

  }

  override def newApp(ast: Z3AST) : Unit = {

  }

  override def newRelevant(ast: Z3AST) : Unit = {
    val aps = fromZ3Formula(ast)
    val fis = functionCallsOf(aps)
    println("As Purescala: " + aps)
    for(fi <- fis) {
      val FunctionInvocation(fd, args) = fi
      println("interesting function call : " + fi)
      if(fd.hasPostcondition) {
        val post = matchToIfThenElse(fd.postcondition.get)
        // FIXME TODO we could use let identifiers here to speed things up a little bit...
        //  val resFresh = FreshIdentifier("resForPostOf" + fd.id.uniqueName, true).setType(fi.getType)
        //  val newLetIDs = fd.args.map(a => FreshIdentifier("argForPostOf" + fd.id.uniqueName, true).setType(a.tpe)).toList
        //  val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*) + (ResultVariable() -> Variable(resFresh))
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*) + (ResultVariable() -> fi)
        // println(substMap)
        val newBody = replace(substMap, post)
        println("I'm going to add this : " + newBody)
        val newAxiom = toZ3Formula(z3, newBody).get
        println("As Z3: " + newAxiom)
        assertAxiom(newAxiom)
      }
    }
  }

  override def restart : Unit = { }
}
