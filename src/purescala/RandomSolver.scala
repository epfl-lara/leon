package purescala

//TODO: improve type error? Actually this is weird it does not seem to have any error of type anymore..
//TODO: Model leads to runtype error

//TODO: Halt must be "thread safe", initialize externalrunning from the solve method is not really correct

import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

import Evaluator._

import scala.util.Random

import scala.sys.error

class RandomSolver(reporter: Reporter, val nbTrial: Option[Int] = None) extends Solver(reporter) {
  require(nbTrial.forall(i => i >= 0))

  val description = "Solver applying random testing"
  override val shortDescription = "random"

  private val startingBound = 2
  private var bound = startingBound
  private val startingThreshold = 20
  private var threshold = startingThreshold

  private val random = new Random()

  private def randomType(): TypeTree = {
    random.nextInt(2) match {
      case 0 => Int32Type
      case 1 => BooleanType
    }
  }

  private def randomValue(t: TypeTree, size: Int): Expr = t match {
    case Int32Type => IntLiteral(size - random.nextInt(2*size + 1))
    case BooleanType => BooleanLiteral(random.nextBoolean())
    case AbstractClassType(acd) => {
      val children = acd.knownChildren
      if(size <= 0) {
        val terminalChildren = children.filter{ 
          case CaseClassDef(_, _, fields) => fields.isEmpty
          case _ => false
        }
        if(terminalChildren.isEmpty) 
          error("We got a problem")
        else
          CaseClass(terminalChildren(random.nextInt(terminalChildren.size)).asInstanceOf[CaseClassDef], Seq())
      } else {
        randomValue(classDefToClassType(children(random.nextInt(children.size))), size)
      }
    }
    case CaseClassType(cd) => {
      CaseClass(cd, cd.fields.map(f => randomValue(f.getType, size - 1))) 
    }
    case AnyType => randomValue(randomType(), size)
    case Untyped => error("I don't know what to do")
    case BottomType => error("I don't know what to do")
    case ListType(base) => error("I don't know what to do")
    case SetType(base) => error("I don't know what to do")
    case TupleType(bases) => error("I don't know what to do")
    case MultisetType(base) => error("I don't know what to do")
    case MapType(from, to) => error("I don't know what to do")
    case OptionType(base) => error("I don't know what to do")
    case f : FunctionType => error("I don't know what to do")
  }

  private var externalRunning = true

  def solve(expression: Expr) : Option[Boolean] = {
    val vars = variablesOf(expression)
    var running = true
    externalRunning = true
    threshold = startingThreshold
    bound = startingBound

    var result: Option[Boolean] = None

    var i = 0
    while(running && externalRunning) {

      nbTrial match {
        case Some(n) => running &&= (i < n)
        case None => ()
      }

      if(i > threshold) {
        threshold *= 2
        bound *= 2
      }

      val var2val: Map[Identifier, Expr] = Map(vars.map(v => (v, randomValue(v.getType, bound))).toList: _*)

      //println("trying with : " + var2val)

      val evalResult = eval(var2val, expression, None)
      evalResult match {
        case OK(BooleanLiteral(true)) => {
          //reporter.info("Example tried but formula was true")
        }
        case OK(BooleanLiteral(false)) => {
          //reporter.info("Example tried and formula was false")
          result = Some(false)
          running = false
        }
        case InfiniteComputation() => {
          reporter.info("Model seems to lead to divergent computation.")
          result = None
          running = false
        }
        case RuntimeError(msg) => {
          reporter.info("Model leads to runtime error: " + msg)
        }
        case t @ TypeError(_,_) => {
          reporter.info("Type error in model evaluation.\n" + t.msg)
        }
        case _ => {
          reporter.info("    -> candidate model discarded.")
          result = None
          running = false
        }
      }

      i += 1
    }
    result
  }

  def halt() {
    externalRunning = false
  }

}
