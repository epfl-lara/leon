package purescala.z3plugins.instantiator

import z3.scala._

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Settings

import purescala.Z3Solver
import purescala.PartialEvaluator

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

class Instantiator(val z3Solver: Z3Solver) extends Z3Theory(z3Solver.z3, "Instantiator") {
  import z3Solver.{z3,program,typeToSort,fromZ3Formula,toZ3Formula}

  val partialEvaluator = new PartialEvaluator(program)

  setCallbacks(
//    reduceApp = true,
    finalCheck = true,
    push = true,
    pop = true,
    newApp = true,
    newAssignment = true,
    newRelevant = true,
//    newEq = true,
//    newDiseq = true,
    reset = true,
    restart = true
  )

  //showCallbacks(true)

  private var functionMap : Map[FunDef,Z3FuncDecl] = Map.empty
  private var reverseFunctionMap : Map[Z3FuncDecl,FunDef] = Map.empty

  protected[purescala] def registerFunction(funDef: FunDef, sorts: Seq[Z3Sort], returnSort: Z3Sort) : Unit = {
    val z3Decl = mkTheoryFuncDecl(z3.mkStringSymbol(funDef.id.uniqueName), sorts, returnSort) 
    functionMap = functionMap + (funDef -> z3Decl)
    reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
  }

  def dumpFunctionMap : Unit = {
    println("REVERSE FUNCTION MAP:")
    println(reverseFunctionMap.toSeq.mkString("\n"))
  }
  def isKnownDef(funDef: FunDef) : Boolean = functionMap.isDefinedAt(funDef)
  def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = {
    functionMap.getOrElse(funDef, scala.Predef.error("No Z3 definition found for function symbol "+ funDef.id.name + " in Instantiator."))
  }
  def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)
  def functionDeclToDef(decl: Z3FuncDecl) : FunDef = {
    reverseFunctionMap.getOrElse(decl, scala.Predef.error("No FunDef found for Z3 definition " + decl + " in Instantiator."))
  }

  // The logic starts here.
  private var stillToAssert : Set[(Int,Expr)] = Set.empty

  override def newAssignment(ast: Z3AST, polarity: Boolean) : Unit = safeBlockToAssertAxioms {
    examineAndUnroll(ast)
  }

  override def newApp(ast: Z3AST) : Unit = {
    examineAndUnroll(ast)
  }

  override def newRelevant(ast: Z3AST) : Unit = {
    //examineAndUnroll(ast)
  }

  private var bodyInlined : Int = 0
  def examineAndUnroll(ast: Z3AST) : Unit = if(bodyInlined < Settings.unrollingLevel) {
    val aps = fromZ3Formula(ast)
    //val fis = functionCallsOf(aps)

    val fis : Set[FunctionInvocation] = aps match {
      case f @ FunctionInvocation(_,_) => Set(f)
      case _ => Set.empty
    }

    //println("As Purescala: " + aps)
    for(fi <- fis) {
      val FunctionInvocation(fd, args) = fi
      //println("interesting function call : " + fi)
      if(bodyInlined < Settings.unrollingLevel && fd.hasPostcondition) {
        bodyInlined += 1
        val post = matchToIfThenElse(fd.postcondition.get)

        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*) + (ResultVariable() -> fi)
        // println(substMap)
        val newBody = partialEvaluator(replace(substMap, post))
        //println("I'm going to add this : " + newBody)
        assertIfSafeOrDelay(newBody)//, isSafe)
      }

      if(bodyInlined < Settings.unrollingLevel && fd.hasBody) {
        bodyInlined += 1
        val body = matchToIfThenElse(fd.body.get)
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*)
        val newBody = replace(substMap, body)
        val theEquality = Equals(fi, partialEvaluator(newBody))
        //println("I'm going to add this : " + theEquality)
        assertIfSafeOrDelay(theEquality)
      }
    }
  }

  override def finalCheck : Boolean = safeBlockToAssertAxioms {
    if(stillToAssert.isEmpty) {
      true
    } else {
      for((lvl,ast) <- stillToAssert) {
        assertAxiomASAP(ast, lvl)
        //assertPermanently(ast)
      }
      stillToAssert = Set.empty
      true
    }
  }

  // This is concerned with how many new function calls the assertion is going
  // to introduce.
  private def assertIfSafeOrDelay(ast: Expr, isSafe: Boolean = false) : Unit = {
    stillToAssert += ((pushLevel, ast))
  }

  // Assert as soon as possible and keep asserting as long as level is >= lvl.
  private def assertAxiomASAP(expr: Expr, lvl: Int) : Unit = assertAxiomASAP(toZ3Formula(z3, expr).get, lvl)
  private def assertAxiomASAP(ast: Z3AST, lvl: Int) : Unit = {
    if(canAssertAxiom) {
      assertAxiomNow(ast)
      //println("(supposed to be available from level " + lvl + ")")
      if(lvl < pushLevel) {
        // Remember to reassert when we backtrack.
        if(pushLevel > 0) {
          rememberToReassertAt(pushLevel - 1, lvl, ast)
        }
      }
    } else {
      toAssertASAP = toAssertASAP + ((lvl, ast))
    }
  }

  private def assertAxiomFrom(ast: Z3AST, level: Int) : Unit = {
    toAssertASAP = toAssertASAP + ((level, ast))
  }

  // private def assertPermanently(expr: Expr) : Unit = {
  //   val asZ3 = toZ3Formula(z3, expr).get

  //   if(canAssertAxiom) {
  //     assertAxiomNow(asZ3)
  //   } else {
  //     toAssertASAP = toAssertASAP + ((0, asZ3))
  //   }
  // }

  private def assertAxiomNow(ast: Z3AST) : Unit = {
    if(!canAssertAxiom)
      println("WARNING ! ASSERTING AXIOM WHEN NOT SAFE !")

    //println("Now asserting : " + ast)
    assertAxiom(ast)
  }

  override def push : Unit = {
    pushLevel += 1
    //println("Now at level " + pushLevel)
  }

  override def pop : Unit = {
    pushLevel -= 1
    //println("Now at level " + pushLevel)

    if(toReassertAt.isDefinedAt(pushLevel)) {
      for((lvl,ax) <- toReassertAt(pushLevel)) {
        assertAxiomFrom(ax, lvl)
      }
      toReassertAt(pushLevel).clear
    }

    assert(pushLevel >= 0)
  }

  override def restart : Unit = {
    pushLevel = 0
  }

  override def reset : Unit = reinit

  // Below is all the machinery to be able to assert axioms in safe states.

  private var pushLevel : Int = _
  private var canAssertAxiom : Boolean = _
  private var toAssertASAP : Set[(Int,Z3AST)] = _
  private val toReassertAt : MutableMap[Int,MutableSet[(Int,Z3AST)]] = MutableMap.empty

  private def rememberToReassertAt(lvl: Int, axLvl: Int, ax: Z3AST) : Unit = {
    if(toReassertAt.isDefinedAt(lvl)) {
      toReassertAt(lvl) += ((axLvl, ax))
    } else {
      toReassertAt(lvl) = MutableSet((axLvl, ax))
    }
  }

  reinit
  private def reinit : Unit = {
    pushLevel = 0
    canAssertAxiom = false
    toAssertASAP = Set.empty
    stillToAssert = Set.empty
  }

  private def safeBlockToAssertAxioms[A](block: => A): A = {
    canAssertAxiom = true

    if (toAssertASAP.nonEmpty) {
      for ((lvl, ax) <- toAssertASAP) {
        if(lvl <= pushLevel) {
          assertAxiomNow(ax)
          //println("(supposed to be available from level " + lvl + ")")
          if(lvl < pushLevel && pushLevel > 0) {
            rememberToReassertAt(pushLevel - 1, lvl, ax)
          }
        }
      }
      toAssertASAP = Set.empty
    }
    
    val result = block
    canAssertAxiom = false
    result
  }
}
