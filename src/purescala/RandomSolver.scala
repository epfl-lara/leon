package purescala

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

  val description = "Solver applying random testing (QuickCheck-like)"
  override val shortDescription = "QC"

  private val random = new Random()

  private def randomType(): TypeTree = {
    random.nextInt(2) match {
      case 0 => Int32Type
      case 1 => BooleanType
    }
  }

  private def randomValue(t: TypeTree, size: Int): Expr = t match {
    case Int32Type => {
      val s = if(size < Int.MaxValue) size + 1 else size
      IntLiteral(random.nextInt(s))
    }
    case BooleanType => BooleanLiteral(random.nextBoolean())
    case AbstractClassType(acd) => {
      val children = acd.knownChildren
      if(size <= 0 || random.nextInt(size) == 1) {
        val terminalChildren = children.filter{ 
          case CaseClassDef(_, _, fields) => fields.isEmpty
          case _ => false
        }
        if(terminalChildren.isEmpty) 
          error("We got a problem")
        else
          CaseClass(terminalChildren(random.nextInt(terminalChildren.size)).asInstanceOf[CaseClassDef], Seq())
      } else {
        val nonTerminalChildren = children.filter{ 
          case CaseClassDef(_, _, fields) => !fields.isEmpty
          case _ => false
        }
        if(nonTerminalChildren.isEmpty) {
          randomValue(classDefToClassType(children(random.nextInt(children.size))), size)
        } else
          randomValue(classDefToClassType(
            nonTerminalChildren(
              random.nextInt(nonTerminalChildren.size))), size)
      }
    }
    case CaseClassType(cd) => {
      val nbFields = cd.fields.size
      CaseClass(cd, cd.fields.map(f => randomValue(f.getType, size / nbFields))) 
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

  def solve(expression: Expr) : Option[Boolean] = {
    val vars = variablesOf(expression)
    val nbVars = vars.size

    var stop = false
    //bound starts at 1 since it allows to test value like 0, 1, and Leaf of class hierarchy
    var bound = 1
    val maxBound = Int.MaxValue
    //the threashold depends on the number of variable and the actual range given by the bound
    val thresholdStep = nbVars * 4
    var threshold = thresholdStep

    var result: Option[Boolean] = None
    var iteration = 0
    while(!forceStop && !stop) {

      nbTrial match {
        case Some(n) => stop &&= (iteration < n)
        case None => ()
      }

      if(iteration > threshold && bound != maxBound) {
        if(bound * 4 < bound) //this is an overflow
          bound = maxBound
        else
          bound *= 2 //exponential growth
        threshold += thresholdStep
      }

      val var2val: Map[Identifier, Expr] = Map(vars.map(v => (v, randomValue(v.getType, bound))).toList: _*)
      //reporter.info("Trying with: " + var2val)

      val evalResult = eval(var2val, expression, None)
      evalResult match {
        case OK(BooleanLiteral(true)) => {
          //continue trying
        }
        case OK(BooleanLiteral(false)) => {
          reporter.info("Found counter example to formula: " + var2val)
          result = Some(false)
          stop = true
        }
        /* in any of the following case, simply continue with another assignement */
        case InfiniteComputation() => {
          //reporter.info("Model seems to lead to divergent computation.")
        }
        case RuntimeError(msg) => {
          //reporter.info("Model leads to runtime error: " + msg)
        }
        case t @ TypeError(_,_) => {
          //reporter.info("Type error in model evaluation.\n" + t.msg)
        }
        case _ => {
          //reporter.info("    -> candidate model discarded.")
        }
      }

      iteration += 1
    }
    result
  }

}
