package leon
package invariant.engine

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet }
import java.io._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{Set => MutableSet}

import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.structure._

/**
   * An enumeration based template generator.
   * Enumerates all numerical terms in some order (this enumeration is incomplete for termination).
   * TODO: Feature:
   * (a) allow template functions and functions with template variables ?
   * (b) should we unroll algebraic data types ?
   *
   * The following function may potentially have complexity O(n^i) where 'n' is the number of functions
   * and 'i' is the increment step
   * TODO: optimize the running and also reduce the size of the input templates
   *
   * For now this is incomplete
   */
class TemplateEnumerator(ctx: InferenceContext) extends TemplateGenerator {
  val prog = ctx.program
  val reporter = ctx.reporter

    //create a call graph for the program
    //Caution: this call-graph could be modified later while call the 'getNextTemplate' method
    private val callGraph = {
      val cg = CallGraphUtil.constructCallGraph(prog)
      cg
    }

	private var tempEnumMap = Map[FunDef, FunctionTemplateEnumerator]()

	def getNextTemplate(fd : FunDef) : Expr = {
	  if(tempEnumMap.contains(fd)) tempEnumMap(fd).getNextTemplate()
	  else {
	    val enumerator = new FunctionTemplateEnumerator(fd, prog, ctx.enumerationRelation,  callGraph, reporter)
	    tempEnumMap += (fd -> enumerator)
	    enumerator.getNextTemplate()
	  }
	}
}

/**
 * This class manages  templates for the given function
 * 'op' is a side-effects parameter
 * Caution: The methods of this class has side-effects on the 'callGraph' parameter
 */
class FunctionTemplateEnumerator(rootFun: FunDef, prog: Program, op: (Expr,Expr) => Expr,
    callGraph : CallGraph,  reporter: Reporter) {
  private val MAX_INCREMENTS = 2
  private val zero = InfiniteIntegerLiteral(0)
  //using default op as <= or == (manually adjusted)
  //private val op = LessEquals
    //LessThan
    //LessEquals
    //Equals.apply _
  private var currTemp: Expr = null
  private var incrStep: Int = 0
  private var typeTermMap = Map[TypeTree, MutableSet[Expr]]()
  private var ttCurrent = Map[TypeTree, MutableSet[Expr]]()

  //get all functions that are not the current function.
  //the value of the current function is given by res and its body
  //itself characterizes how it is defined recursively w.r.t itself.
  //Need to also avoid mutual recursion as it may lead to proving of invalid facts
  private val fds = prog.definedFunctions.filter(_ != rootFun)

  def getNextTemplate(): Expr = {
    //println("Getting next template for function: "+fd.id)

    if (incrStep == MAX_INCREMENTS){
      //exhausted the templates, so return
      op(currTemp, zero)
    }
    else {

      incrStep += 1

      var newTerms = Map[TypeTree, MutableSet[Expr]]()
      if (currTemp == null) {
        //initialize
        //add all the arguments and results of fd to 'typeTermMap'
        rootFun.params.foreach((vardecl) => {
          val tpe = vardecl.getType
          val v = vardecl.id.toVariable
          if (newTerms.contains(tpe)) {
            newTerms(tpe).add(v)
          } else {
            newTerms += (tpe -> MutableSet(v))
          }
        })

        val resVar = Util.getFunctionReturnVariable(rootFun)
        if (newTerms.contains(rootFun.returnType)) {
          newTerms(rootFun.returnType).add(resVar)
        } else {
          newTerms += (rootFun.returnType -> MutableSet(resVar))
        }

        //also 'assignCurrTemp' to a template variable
        currTemp = TemplateIdFactory.freshTemplateVar()
      } else {

        //apply the user-defined functions to the compatible terms in typeTermMap
        //Important: Make sure that the recursive calls are not introduced in the templates
        //TODO: this is a hack to prevent infinite recursion in specification. However, it is not clear if this will prevent inferrence of
        //any legitimate specifications (however this can be modified).
        fds.foreach((fun) => {
          //Check if adding a call from 'rootFun' to 'fun' creates a mutual recursion by checking if
          //'fun' transitively calls 'rootFun'
          if (fun != rootFun && !callGraph.transitivelyCalls(fun, rootFun)) {

            //check if every argument has at least one satisfying assignment?
            if (fun.params.filter((vardecl) => !ttCurrent.contains(vardecl.getType)).isEmpty) {

              //here compute all the combinations
              val newcalls = generateFunctionCalls(fun)
              if (newTerms.contains(fun.returnType)) {
                newTerms(fun.returnType) ++= newcalls
              } else {
                var muset = MutableSet[Expr]()
                muset ++= newcalls
                newTerms += (fun.returnType -> muset)
              }
            }
          }

        })

      }
      //add all the newly generated expression to the typeTermMap
      ttCurrent = newTerms
      typeTermMap ++= newTerms

      //statistics
      reporter.info("- Number of new terms enumerated: " + newTerms.size)

      //return all the integer valued terms of newTerms
      //++ newTerms.getOrElse(Int32Type, Seq[Expr]()) (for now not handling int 32 terms)
      val numericTerms = (newTerms.getOrElse(RealType, Seq[Expr]()) ++ newTerms.getOrElse(IntegerType, Seq[Expr]())).toSeq
      if(!numericTerms.isEmpty) {
        //create a linear combination of intTerms
        val newTemp = numericTerms.foldLeft(null: Expr)((acc, t: Expr) => {
          val summand = Times(t, TemplateIdFactory.freshTemplateVar() : Expr)
          if (acc == null) summand
          else
            Plus(summand, acc)
        })
        //add newTemp to currTemp
        currTemp = Plus(newTemp, currTemp)

        //get all the calls in the 'newTemp' and add edges from 'rootFun' to the callees to the call-graph
        val callees = CallGraphUtil.getCallees(newTemp)
        callees.foreach(callGraph.addEdgeIfNotPresent(rootFun, _))
      }
      op(currTemp, zero)
    }
  }

  /**
   * Generate a set of function calls of fun using the terms in ttCurrent
   */
  def generateFunctionCalls(fun: FunDef): Set[Expr] = {
    /**
     * To be called with argIndex of zero and an empty argList
     */
    def genFunctionCallsRecur(argIndex: Int, argList: Seq[Expr]): Set[Expr] = {
      if (argIndex == fun.params.size) {
        //create a call using argList
        //TODO: how should we handle generics
        Set(FunctionInvocation(TypedFunDef(fun, fun.tparams.map(_.tp)), argList))
      } else {
        val arg = fun.params(argIndex)
        val tpe = arg.getType
        ttCurrent(tpe).foldLeft(Set[Expr]())((acc, term) => acc ++ genFunctionCallsRecur(argIndex + 1, argList :+ term))
      }
    }

    genFunctionCallsRecur(0, Seq())
  }
}