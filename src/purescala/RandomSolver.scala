package purescala

//TODO: improve type error? Actually this is weird it does not seem to have any error of type anymore..
//TODO: Model leads to runtype error

import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

import Evaluator._

import scala.util.Random

class RandomSolver(reporter: Reporter, val nbTrial: Option[Int] = None) extends Solver(reporter) {
  require(nbTrial.forall(i => i >= 0))

  val description = "Solver applying random testing"
  override val shortDescription = "random"

  private def randomType(): TypeTree = {
    (new Random()).nextInt(2) match {
      case 0 => Int32Type
      case 1 => BooleanType
    }
  }

  private def randomValueGen(): (TypeTree) => Expr = {
    val random = new Random()
    var nbIntGenerated = 0
    
    def res(tpe: TypeTree): Expr = tpe match {
      case Int32Type => {
        val r = nbIntGenerated match {
          case 0 => IntLiteral(0)
          case 1 => IntLiteral(1)
          case _ => IntLiteral(random.nextInt())
        }
        nbIntGenerated += 1
        r
      }
      case BooleanType => BooleanLiteral(random.nextBoolean())

      case AbstractClassType(acd) => {
        val children = acd.knownChildren
        res(classDefToClassType(children(random.nextInt(children.size))))
      }
      case CaseClassType(cd) => CaseClass(cd, cd.fields.map(f => res(f.getType))) 
      case AnyType => res(randomType())
      case Untyped => error("I don't know what to do")
      case BottomType => error("I don't know what to do")
      case ListType(base) => error("I don't know what to do")
      case SetType(base) => error("I don't know what to do")
      case TupleType(bases) => error("I don't know what to do")
      case MultisetType(base) => error("I don't know what to do")
      case MapType(from, to) => error("I don't know what to do")
      case OptionType(base) => error("I don't know what to do")    
    }
    res
  }

  private var running = true

  def solve(expression: Expr) : Option[Boolean] = {
    //println("solving: " + expression)
    val vars = variablesOf(expression)
    val randomValue = randomValueGen()
    running = true

    var result: Option[Boolean] = None

    var i = 0
    while(running) {

      nbTrial match {
        case Some(n) => running &&= (i < n)
        case None => ()
      }

      val var2val: Map[Identifier, Expr] = Map(vars.map(v => (v, randomValue(v.getType))).toList: _*)

      //println("trying with : " + var2val)

      val evalResult = eval(var2val, expression, None)
      evalResult match {
        case OK(BooleanLiteral(true)) => {
          reporter.info("Example tried but formula was true")
        }
        case OK(BooleanLiteral(false)) => {
          reporter.info("Example tried and formula was false")
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
    running = false
  }

}
