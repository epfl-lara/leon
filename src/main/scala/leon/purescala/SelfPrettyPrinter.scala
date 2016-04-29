/* Copyright 2009-2016 EPFL, Lausanne */

package leon.purescala

import leon.purescala
import leon.solvers.{ Model, SolverFactory }
import leon.LeonContext
import leon.evaluators
import leon.utils.StreamUtils
import leon.purescala.Quantification._
import leon.utils.DebugSectionEvaluation
import purescala.Definitions.Program
import purescala.Expressions._
import purescala.Types.StringType
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Expressions._
import purescala.Expressions.{Choose }
import purescala.Extractors._
import purescala.TypeOps._
import purescala.Types._
import purescala.Common._
import purescala.Definitions._
import scala.collection.mutable.ListBuffer
import leon.evaluators.DefaultEvaluator

object SelfPrettyPrinter {
  def prettyPrintersForType(inputType: TypeTree)(implicit ctx: LeonContext, program: Program): Stream[Lambda] = {
    (new SelfPrettyPrinter).prettyPrintersForType(inputType)
  }
  def print(v: Expr, orElse: =>String, excluded: Set[FunDef] = Set())(implicit ctx: LeonContext, program: Program): String = {
    (new SelfPrettyPrinter).print(v, orElse, excluded)
  }
}

/** This pretty-printer uses functions defined in Leon itself.
  * If not pretty printing function is defined, return the default value instead
  */
class SelfPrettyPrinter {
  implicit val section = leon.utils.DebugSectionEvaluation
  private var allowedFunctions = Set[FunDef]()
  private var excluded = Set[FunDef]()
  /** Functions whose name does not need to end with `tostring` or which can be abstract, i.e. which may contain a choose construct.*/
  def allowFunction(fd: FunDef) = { allowedFunctions += fd; this }
  
  def excludeFunctions(fds: Set[FunDef]) = { excluded ++= fds; this }
  def excludeFunction(fd: FunDef) = { excluded += fd; this }

  /** Returns a list of possible lambdas that can transform the input type to a String.
    * At this point, it does not consider yet the inputType. Only [[prettyPrinterFromCandidate]] will consider it. */
  def prettyPrintersForType(inputType: TypeTree/*, existingPp: Map[TypeTree, List[Lambda]] = Map()*/)(implicit ctx: LeonContext, program: Program): Stream[Lambda] = {
    program.definedFunctions.toStream flatMap { fd =>
      val isCandidate =
        fd.returnType == StringType &&
        fd.params.nonEmpty &&
        !excluded(fd) &&
        (allowedFunctions(fd) || fd.id.name.toLowerCase().endsWith("tostring"))

      if(isCandidate) {
        prettyPrinterFromCandidate(fd, inputType)
      } else {
        Stream.Empty
      }
    }
  }
  
  
  def prettyPrinterFromCandidate(fd: FunDef, inputType: TypeTree)(implicit ctx: LeonContext, program: Program): Stream[Lambda] = {
    TypeOps.canBeSubtypeOf(inputType, fd.tparams.map(_.tp), fd.params.head.getType) match {
      case Some(genericTypeMap) => 
        val defGenericTypeMap = genericTypeMap.map{ case (k, v) => (Definitions.TypeParameterDef(k), v) }
        def gatherPrettyPrinters(funIds: List[Identifier], acc: ListBuffer[Stream[Lambda]] = ListBuffer()): Option[Stream[List[Lambda]]] = funIds match {
          case Nil => Some(StreamUtils.cartesianProduct(acc.toList))
          case funId::tail => // For each function, find an expression which could be provided if it exists.
            funId.getType match {
              case FunctionType(Seq(in), StringType) => // Should have one argument.
                val candidates = prettyPrintersForType(in)
                gatherPrettyPrinters(tail, acc += candidates)
              case _ => None
            }
        }
        val funIds = fd.params.tail.map(x => TypeOps.instantiateType(x.id, defGenericTypeMap)).toList
        gatherPrettyPrinters(funIds) match {
          case Some(l) => for(lambdas <- l) yield {
            val x = FreshIdentifier("x", inputType) // verify the type
            Lambda(Seq(ValDef(x)), functionInvocation(fd, Variable(x)::lambdas))
          }
          case _ => Stream.empty
        }
      case None => Stream.empty
    }
  }


  /** Actually prints the expression with as alternative the given orElse
    * @param excluded The list of functions which should be excluded from pretty-printing
    *                 (to avoid rendering counter-examples of toString methods using the method itself)
    * @return a user defined string for the given typed expression.
    **/
  def print(v: Expr, orElse: =>String, excluded: Set[FunDef] = Set())(implicit ctx: LeonContext, program: Program): String = {
    this.excluded = excluded
    val s = prettyPrintersForType(v.getType)   // TODO: Included the variable excluded if necessary.
    s.take(100).find {
      // Limit the number of pretty-printers.
      case Lambda(_, FunctionInvocation(TypedFunDef(fd, _), _)) =>
        (program.callGraph.transitiveCallees(fd) + fd).forall { fde =>
          !ExprOps.exists(_.isInstanceOf[Choose])(fde.fullBody)
        }
      case _ => false
    } match {
      case None => orElse
      case Some(Lambda(Seq(ValDef(id)), body)) =>
        ctx.reporter.debug("Executing pretty printer for type " + v.getType + " : " + v + " on " + v)
        val ste = new DefaultEvaluator(ctx, program)
        try {
          val result = ste.eval(body, Map(id -> v))
          
          result.result match {
            case Some(StringLiteral(res)) if res != "" =>
              res
            case res =>
              ctx.reporter.debug("not a string literal "  + result)
              orElse
          }
        } catch {
          case e: evaluators.ContextualEvaluator#EvalError =>
            ctx.reporter.debug("Error "  + e.msg)
            orElse
        }
    }
  }
}
