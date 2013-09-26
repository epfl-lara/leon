package lesynth

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers._

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import java.io.{ BufferedWriter, FileWriter, File }
import leon.evaluators.CodeGenEvaluator
import leon.purescala.TreeOps
import leon.purescala.Common._
import leon.codegen.CodeGenEvalParams
import leon.purescala.TypeTrees._
import leon.evaluators.EvaluationResults._

import lesynth.examples.InputExamples
import lesynth.evaluation.CodeGenEvaluationStrategy
import lesynth.ranking.Candidate
import insynth.reconstruction.Output
import lesynth.examples.Example

import _root_.util.Scaffold

// TODO codegen evaluator params should be used but not yet in master
class EvaluationTest extends FunSuite {

  import Scaffold._

  val mergeSortWithTwoExamples = """
				import leon.Utils._
				
				object MergeSort {
				  sealed abstract class List
				  case class Cons(head: Int, tail: List) extends List
				  case class Nil() extends List
				
				  sealed abstract class PairAbs
				  case class Pair(fst: List, snd: List) extends PairAbs
				
				  def contents(l: List): Set[Int] = l match {
				    case Nil() => Set.empty
				    case Cons(x, xs) => contents(xs) ++ Set(x)
				  }
				
				  def isSorted(l: List): Boolean = l match {
				    case Nil() => true
				    case Cons(x, xs) => xs match {
				      case Nil() => true
				      case Cons(y, ys) => x <= y && isSorted(Cons(y, ys))
				    }
				  }
				
				  def size(list: List): Int = list match {
				    case Nil() => 0
				    case Cons(x, xs) => 1 + size(xs)
				  }
				
				  def splithelper(aList: List, bList: List, n: Int): Pair = {
				    if (n <= 0) Pair(aList, bList)
				    else
				      bList match {
				        case Nil() => Pair(aList, bList)
				        case Cons(x, xs) => splithelper(Cons(x, aList), xs, n - 1)
				      }
				  } ensuring (res =>
				  	contents(aList) ++ contents(bList) == contents(res.fst) ++ contents(res.snd)
				  	&&
				  	size(aList) + size(bList) == size(res.fst) + size(res.snd)
				  )
				
				  def split(list: List): Pair = {
				    splithelper(Nil(), list, 2)
				  } ensuring (res =>
				  	contents(list) == contents(res.fst) ++ contents(res.snd)
				  	&&
				  	size(list) == size(res.fst) + size(res.snd)
				  )
				
				  def merge(aList: List, bList: List): List = {
				    require(isSorted(aList) && isSorted(bList))
				    bList match {
				      case Nil() => aList
				      case Cons(x, xs) =>
				        aList match {
				          case Nil() => bList
				          case Cons(y, ys) =>
				            if (y < x)
				              Cons(y, merge(ys, bList))
				            else
				              
				              Cons(x, merge(aList, xs))
				        }
				    }
				  } ensuring (res => contents(res) ==
				    contents(aList) ++ contents(bList) && isSorted(res) &&
				    size(res) == size(aList) + size(bList)
				  )
				
				  def isEmpty(list: List): Boolean = list match {
				    case Nil() => true
				    case Cons(x, xs) => false
				  }
				
				  def sort(list: List): List = choose {
				    (res: List) =>
				      contents(res) == contents(list) && isSorted(res) && size(res) == size(list)
				  } ensuring ( res => contents(res) == contents(list) && isSorted(res) && size(res) == size(list))			
  	    
  	    	def testFun1(list: List) = {
		  	    if (isEmpty(list))
						  list
						else
						  if (isSorted(list))
						    list
						  else
						    splithelper(Nil(), list, size(list)).fst
  				}				
  	    
  	    	def testFun2(list: List) = {
  	    		if (isEmpty(list))
						  list
						else
						  if (isSorted(list))
						    list
						  else
						    merge(sort(split(list).fst), sort(split(list).snd))
  				}
				}		
	    """

  test("codegen strategy") {

    for ((sctx, funDef, problem) <- forProgram(mergeSortWithTwoExamples)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      expectResult(1) { problem.xs.size }
      val resultVariable = problem.xs.head

      val codeGenEval = new CodeGenEvaluator(sctx.context, program)
      def inputExamples =
        InputExamples.getDataGenInputExamples(sctx.context, program, codeGenEval, problem,
          20, 2000, Some(arguments)).map(Example(_))

      import TreeOps._
      def replaceFun(expr: Expr) = expr match {
        case Variable(id) if id.name == "list" =>
          Some(Variable(arguments.head))
        //  	    case FunctionInvocation(`funDef`, args) =>
        //  	      FunctionInvocation(funDef, )
        case _ => None
      }

      val body1 =
        searchAndReplace(replaceFun)(
          program.definedFunctions.find(_.id.name == "testFun1").get.body.get)

      val body2 =
        searchAndReplace(replaceFun)(
          program.definedFunctions.find(_.id.name == "testFun2").get.body.get)

      val evaluationStrategy = new CodeGenEvaluationStrategy(program, funDef, sctx.context, 500)

      val candidates = IndexedSeq(body1, body2) map (b => Output(b, 0))

      val ranker = evaluationStrategy.getRanker(candidates, identity, inputExamples)
      val exampleRunner = evaluationStrategy.exampleRunner

      val eval1 = (for (ind <- 0 until inputExamples.size) yield {
        val res = exampleRunner.evaluate(0, ind)
        (res, exampleRunner.examples(ind))
      })

      val eval2 = (for (ind <- 0 until inputExamples.size) yield {
        val res = exampleRunner.evaluate(1, ind)
        (res, exampleRunner.examples(ind))
      })

      val message = "Examples: " + inputExamples.mkString(", ")
      val eval1message = "Evaluation of " + body1 + " yielded: " + eval1.mkString("\n")
      val eval2message = "Evaluation of " + body2 + " yielded: " + eval2.mkString("\n")
      assert(inputExamples.size == eval2.count(_._1), message + " " + eval2message)
      assert(inputExamples.size > eval1.count(_._1), message + " " + eval1message)
    }
  }

  test("codegen evaluator") {

    for ((sctx, funDef, problem) <- forProgram(mergeSortWithTwoExamples)) {
      val program = sctx.program
      val arguments = funDef.args.map(_.id)

      expectResult(1) { problem.xs.size }
      val resultVariable = problem.xs.head

      val codeGenEval = new CodeGenEvaluator(sctx.context, program)
      def inputExamples =
        InputExamples.getDataGenInputExamples(sctx.context, program, codeGenEval, problem,
          20, 2000, Some(arguments)).map(Example(_))

      import TreeOps._
      def replaceFun(expr: Expr) = expr match {
        case Variable(id) if id.name == "list" =>
          Some(Variable(arguments.head))
        case _ => None
      }

      val body1 =
        searchAndReplace(replaceFun)(
          program.definedFunctions.find(_.id.name == "testFun1").get.body.get)
      val body2 =
        searchAndReplace(replaceFun)(
          program.definedFunctions.find(_.id.name == "testFun2").get.body.get)

      // evaluate expressions with let
      {
        def formExecutable(expr: Expr) = {

          import TreeOps._

          val newFunId = FreshIdentifier("tempIntroducedFunction")
          val newFun = new FunDef(newFunId, funDef.returnType, funDef.args)
          newFun.precondition = funDef.precondition
          newFun.postcondition = funDef.postcondition

          def replaceFunDef(expr: Expr) = expr match {
            case FunctionInvocation(`funDef`, args) =>
              Some(FunctionInvocation(newFun, args))
            case _ => None
          }
          val newBody = searchAndReplace(replaceFunDef)(expr)

          newFun.body = Some(newBody)

          assert(expr.getType != Untyped)
          val resFresh = FreshIdentifier("result") //.setType(expr.getType)
          resFresh.setType(newBody.getType)

          val (id, post) = newFun.postcondition.get
          // body can contain (self-)recursive calls
          (
            Let(resFresh, newBody,
              replace(Map(Variable(id) -> Variable(resFresh)),
                matchToIfThenElse(post))),
              newFun)
        }

        val pairs = List(body1, body2) map (formExecutable(_))
        val candidates = pairs map (_._1)

        val params = CodeGenEvalParams(maxFunctionInvocations = 500, checkContracts = true)

        val evaluator = new CodeGenEvaluator(sctx.context,
          program.copy(mainObject = program.mainObject.copy(defs = program.mainObject.defs ++ pairs.map(_._2)))
          /*, params*/)

        val eval1 = (for (ind <- 0 until inputExamples.size) yield {
          val res = evaluator.eval(candidates(0), inputExamples(ind).map)
          (res, inputExamples(ind))
        })

        val eval2 = (for (ind <- 0 until inputExamples.size) yield {
          val res = evaluator.eval(candidates(1), inputExamples(ind).map)
          (res, inputExamples(ind))
        })

        val message = "Examples: " + inputExamples.mkString(", ")
        val eval1message = "Evaluation of " + body1 + " yielded: " + eval1.mkString("\n")
        val eval2message = "Evaluation of " + body2 + " yielded: " + eval2.mkString("\n")
        assert(inputExamples.size == eval2.count(_._1 == Successful(BooleanLiteral(true))), message + " " + eval2message)
        assert(inputExamples.size > eval1.count(_._1 == Successful(BooleanLiteral(true))), message + " " + eval1message)
      }

      // evaluate expressions without let
      {
        def formExecutable(expr: Expr) = {

          import TreeOps._

          val newFunId = FreshIdentifier("tempIntroducedFunction")
          val newFun = new FunDef(newFunId, funDef.returnType, funDef.args)
          newFun.precondition = funDef.precondition
          newFun.postcondition = funDef.postcondition

          def replaceFunDef(expr: Expr) = expr match {
            case FunctionInvocation(`funDef`, args) =>
              Some(FunctionInvocation(newFun, args))
            case _ => None
          }
          val newBody = searchAndReplace(replaceFunDef)(expr)

          newFun.body = Some(newBody)

          assert(expr.getType != Untyped)
          val resFresh = FreshIdentifier("result") //.setType(expr.getType)
          resFresh.setType(newBody.getType)

          // body can contain (self-)recursive calls
          (newBody, newFun)
        }

        val pairs = List(body1, body2) map (formExecutable(_))
        val candidates = pairs map (_._1)

        val params = CodeGenEvalParams(maxFunctionInvocations = 500, checkContracts = true)

        val evaluator = new CodeGenEvaluator(sctx.context,
          program.copy(mainObject = program.mainObject.copy(defs = program.mainObject.defs ++ pairs.map(_._2)))
          /*, params*/)

        val eval1 = (for (ind <- 0 until inputExamples.size) yield {
          val res = evaluator.eval(candidates(0), inputExamples(ind).map)
          (res, inputExamples(ind))
        })

        val eval2 = (for (ind <- 0 until inputExamples.size) yield {
          val res = evaluator.eval(candidates(1), inputExamples(ind).map)
          (res, inputExamples(ind))
        })

        val message = "Examples: " + inputExamples.mkString(", ")
        val eval1message = "Evaluation of " + body1 + " yielded: " + eval1.mkString("\n")
        val eval2message = "Evaluation of " + body2 + " yielded: " + eval2.mkString("\n")
//        assert(inputExamples.size == eval2.count(_._1 == Successful(BooleanLiteral(true))), message + " " + eval2message)
//        assert(inputExamples.size > eval1.count(_._1 == Successful(BooleanLiteral(true))), message + " " + eval1message)
      }
    }
  }
}