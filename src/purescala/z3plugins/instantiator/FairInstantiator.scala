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
import scala.collection.mutable.PriorityQueue

class FairInstantiator(val z3Solver: Z3Solver) extends Z3Theory(z3Solver.z3, "FairInstantiator") with AbstractInstantiator {
  import z3Solver.{z3,program,typeToSort,fromZ3Formula,toZ3Formula}

  val partialEvaluator = new PartialEvaluator(program)

  setCallbacks(
//    reduceApp = true,
    finalCheck = true,
    push = true,
    pop = true,
    newApp = true,
    newAssignment = true,
    //newRelevant = true,
    newEq = true,
    newDiseq = true,
    reset = true,
    restart = true
  )

  //showCallbacks(true)

  // Related to creating and recovering Z3 function symbols
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

  // Related to discovering function calls and adding instantiations
  private var queue : PriorityQueue[Unrolling] = new PriorityQueue[Unrolling]()(UnrollingOrdering)
//  private var stillToAssert : List[(Int,Expr)] = Nil

  override def newAssignment(ast: Z3AST, polarity: Boolean) : Unit = safeBlockToAssertAxioms {
    examineAndUnroll(ast)
  }

  // Just using these to assert axioms early when possible...
  override def newEq(ast1: Z3AST, ast2: Z3AST) : Unit = safeBlockToAssertAxioms {}
  override def newDiseq(ast1: Z3AST, ast2: Z3AST) : Unit = safeBlockToAssertAxioms {}

  override def newApp(ast: Z3AST) : Unit = {
    examineAndUnroll(ast)
  }

  override def newRelevant(ast: Z3AST) : Unit = {
    // WARNING : CURRENTLY NOT CALLED !
    //examineAndUnroll(ast)
  }

  private var bodyInlined : Int = 0
  private var seen : Set[Z3AST] = Set.empty
  private var seenCount : Int = 0
  def examineAndUnroll(ast: Z3AST, allFunctions: Boolean = false) : Unit = if(bodyInlined < Settings.unrollingLevel) {
    if(seen(ast)) {
      seenCount += 1
//      println(" HIT ! seenCount now at " + seenCount)
      return
    } else {
      seen += ast
    }

    val aps = fromZ3Formula(ast)
    val fis : Set[FunctionInvocation] = if(allFunctions) {
      functionCallsOf(aps)
    } else {
      aps match {
        case f @ FunctionInvocation(_,_) => Set(f)
        case _ => Set.empty
      }
    }
    
    println("Examining : " + ast)
    println("As Purescala: " + aps)
    for(fi <- fis) {
      val FunctionInvocation(fd, args) = fi

      if(!program.isRecursive(fd)) {
        println("We have a non-recursive function, we could just inline it !")
        println(fi)
        println("...I'm just saying.")
      }

      if(bodyInlined < Settings.unrollingLevel && fd.hasPostcondition) {
        bodyInlined += 1
        val post = matchToIfThenElse(fd.postcondition.get)

        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*) + (ResultVariable() -> fi)
        val newBody = partialEvaluator(replace(substMap, post))

        val unrolling = new Unrolling(fi, newBody, true, pushLevel)
        queue += unrolling

        //assertIfSafeOrDelay(newBody)//, isSafe)
      }

      if(bodyInlined < Settings.unrollingLevel && fd.hasBody) {
        bodyInlined += 1
        val body = matchToIfThenElse(fd.body.get)
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*)
        val newBody = partialEvaluator(replace(substMap, body))
        // val theEquality = Equals(fi, newBody)

        val unrolling = new Unrolling(fi, newBody, false, pushLevel)
        //println("Now enqueuing, for function " + fd.id.name + ", with depth:  " + unrolling.depth)
        //println(newBody)

        queue += unrolling

        //assertIfSafeOrDelay(theEquality)
      }
    }
  }

  override def finalCheck : Boolean = safeBlockToAssertAxioms {
    if(!queue.isEmpty) {
      while(!queue.isEmpty && queue.head.depth <= deepestAuthorized) {
        val highest : Unrolling = queue.dequeue()
        val toConvertAndAssert = if(highest.isContract) {
          highest.body
        } else {
          Equals(highest.invocation, highest.body)
        }
        // println("Now will be asserting :")
        println(Console.RED + toConvertAndAssert + Console.RESET)
        assertAxiomASAP(toZ3Formula(z3, toConvertAndAssert).get, 0)
      }
    }
//    stillToAssert = Nil
    true
/*
    if(stillToAssert.isEmpty) {
      true
    } else {
      for((lvl,ast) <- stillToAssert.reverse) {
        assertAxiomASAP(ast, lvl)
        //assertPermanently(ast)
      }
      stillToAssert = Nil
      true
    }
*/
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

  private var deepestAuthorized : Int = -1
  def possibleContinuation : Boolean = !queue.isEmpty || deepestAuthorized <= 0
  def increaseSearchDepth() : Unit = { deepestAuthorized += 1; bodyInlined = 0 }

  reinit
  private def reinit : Unit = {
    pushLevel = 0
    canAssertAxiom = false
    toAssertASAP = Set.empty
 //   stillToAssert = Nil
    queue.clear
  }

  private def safeBlockToAssertAxioms[A](block: => A): A = {
    canAssertAxiom = true

    if (toAssertASAP.nonEmpty) {
      // println("In a safe block. " + toAssertASAP.size + " axioms to add.")
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

  private object UnrollingOrdering extends Ordering[Unrolling] {
    def compare(u1: Unrolling, u2: Unrolling) : Int = {
      u2.depth - u1.depth
    }
  }

  private class Unrolling(val invocation: FunctionInvocation, val body: Expr, val isContract: Boolean, val fromLevel: Int) {
    // the maximal depth of selector calls in arguments of the invocation
    val depth : Int = if(!program.isRecursive(invocation.funDef)) {
      0
    } else {
      measureADTChildrenDepth(invocation)
    }
    println("unrolling built. It has depth " + depth + "\n" + invocation)
  }
  private object Unrolling {
    def unapply(u: Unrolling) : Option[(FunctionInvocation,Expr)] = if(u != null) {
      Some((u.invocation, u.body))
    } else {
      None
    }
  }
}
