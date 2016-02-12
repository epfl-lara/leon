package leon.purescala

import leon.purescala
import leon.solvers.{ HenkinModel, Model, SolverFactory }
import leon.LeonContext
import leon.evaluators
import leon.utils.StreamUtils
import leon.purescala.Quantification._
import leon.utils.DebugSectionSynthesis
import leon.utils.DebugSectionVerification
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
  * @param The list of functions which should be excluded from pretty-printing (to avoid rendering counter-examples of toString methods using the method itself)
  * @return a user defined string for the given typed expression. */
class SelfPrettyPrinter {
  private var allowedFunctions = Set[FunDef]()
  private var excluded = Set[FunDef]()
  /** Functions whose name does not need to end with `tostring` or which can be abstract, i.e. which may contain a choose construct.*/
  def allowFunction(fd: FunDef) = { allowedFunctions += fd; this }
  
  def excludeFunctions(fds: Set[FunDef]) = { excluded ++= fds; this }
  def excludeFunction(fd: FunDef) = { excluded += fd; this }

  /** Returns a list of possible lambdas that can transform the input type to a String*/
  def prettyPrintersForType(inputType: TypeTree/*, existingPp: Map[TypeTree, List[Lambda]] = Map()*/)(implicit ctx: LeonContext, program: Program): Stream[Lambda] = {
    // Use the other argument if you need recursive typing (?)
    program.definedFunctions.toStream flatMap {
      fd =>
        val isCandidate = fd.returnType == StringType &&
        fd.params.length >= 1 &&
        !excluded(fd) &&
        (allowedFunctions(fd) || (
        //TypeOps.isSubtypeOf(v.getType, fd.params.head.getType) &&
        fd.id.name.toLowerCase().endsWith("tostring") &&
        program.callGraph.transitiveCallees(fd).forall { fde => 
          !purescala.ExprOps.exists( _.isInstanceOf[Choose])(fde.fullBody)
        }))
        if(isCandidate) {
          prettyPrinterFromCandidate(fd, inputType)
        } else Stream.Empty
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
            val x = FreshIdentifier("x", fd.params.head.getType) // verify the type
            Lambda(Seq(ValDef(x)), functionInvocation(fd, Variable(x)::lambdas))
          }
          case _ => Stream.empty
        }
      case None => Stream.empty
    }
  }
  
  
  /** Actually prints the expression with as alternative the given orElse */
  def print(v: Expr, orElse: =>String, excluded: Set[FunDef] = Set())(implicit ctx: LeonContext, program: Program): String = {
    this.excluded = excluded
    val s = prettyPrintersForType(v.getType)   // TODO: Included the variable excluded if necessary.
    if(s.isEmpty) {
      orElse
    } else {
      val l: Lambda = s.head
      println("Executing pretty printer for type " + v.getType + " : " + l + " on " + v)
      val ste = new DefaultEvaluator(ctx, program)
      try {
        val toEvaluate = application(l, Seq(v))
        val result = ste.eval(toEvaluate)
        
        result.result match {
          case Some(StringLiteral(res)) if res != "" =>
            res
          case res =>
            println("not a string literal "  + res)
            orElse
        }
      } catch {
        case e: evaluators.ContextualEvaluator#EvalError =>
          println("Error "  + e.msg)
          orElse
      }
    }
  }
}