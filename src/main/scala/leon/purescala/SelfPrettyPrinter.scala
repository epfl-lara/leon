/* Copyright 2009-2016 EPFL, Lausanne */

package leon.purescala

import Constructors._
import Expressions._
import Types._
import Common._
import Definitions._
import leon.evaluators._
import leon.LeonContext
import leon.utils.StreamUtils

import scala.collection.mutable.ListBuffer

object SelfPrettyPrinter {
  def prettyPrintersForType(inputType: TypeTree)(implicit ctx: LeonContext, program: Program): Stream[Lambda] = {
    (new SelfPrettyPrinter).prettyPrintersForType(inputType)
  }
  def print(v: Expr, orElse: =>String, excluded: Set[FunDef] = Set())(implicit ctx: LeonContext, program: Program): String = {
    (new SelfPrettyPrinter).print(v, orElse, excluded)
  }
}

/** T is the type of pretty-printers which have to be found (e.g. Lambda or Lambdas with identifiers)
 *  U is the type of the arguments during gathering */
trait PrettyPrinterFinder[T, U >: T] {
  protected def isExcluded(fd: FunDef): Boolean
  protected def isAllowed(fd: FunDef): Boolean
  
  @inline def isValidPrinterName(s: String) = { val n = s.toLowerCase(); n.endsWith("tostring") || n.endsWith("mkstring") }
  
  @inline def isCandidate(fd: FunDef) = fd.returnType == StringType &&
        fd.params.nonEmpty &&
        !isExcluded(fd) &&
        (isAllowed(fd) || isValidPrinterName(fd.id.name))

  /** Returns a list of possible lambdas that can transform the input type to a String.
    * At this point, it does not consider yet the inputType. Only [[prettyPrinterFromCandidate]] will consider it. */
  def prettyPrintersForType(inputType: TypeTree/*, existingPp: Map[TypeTree, List[Lambda]] = Map()*/)(implicit ctx: LeonContext, program: Program): Stream[T] = {
    program.definedFunctions.toStream flatMap { fd =>
      if(isCandidate(fd)) prettyPrinterFromCandidate(fd, inputType) else Stream.Empty
    }
  }
  
  def getPrintersForType(t: TypeTree)(implicit ctx: LeonContext, program: Program): Option[Stream[U]] = t match {
    case FunctionType(Seq(in), StringType) => // Should have one argument.
      Some(prettyPrintersForType(in))
    case _ => None
  }
  
  // To Implement
  def buildLambda(inputType: TypeTree, fd: FunDef, slu: Stream[List[U]]): Stream[T]
  
  def prettyPrinterFromCandidate(fd: FunDef, inputType: TypeTree)(implicit ctx: LeonContext, program: Program): Stream[T] = {
    TypeOps.subtypingInstantiation(inputType, fd.params.head.getType) match {
      case Some(genericTypeMap) =>
        //println("Found a mapping")
        def gatherPrettyPrinters(funIds: List[Identifier], acc: ListBuffer[Stream[U]] = ListBuffer[Stream[U]]()): Option[Stream[List[U]]] = funIds match {
          case Nil => Some(StreamUtils.cartesianProduct(acc.toList))
          case funId::tail => // For each function, find an expression which could be provided if it exists.
            getPrintersForType(funId.getType) match {
              case Some(u) => gatherPrettyPrinters(tail, acc += u)
              case None    =>
                None
            }
        }
        val funIds = fd.params.tail.map(x => TypeOps.instantiateType(x.id, genericTypeMap)).toList
        gatherPrettyPrinters(funIds) match {
          case Some(l) => buildLambda(inputType, fd, l)
          case None =>    Stream.empty
        }
      case None =>        Stream.empty
    }
  }
}

/** This pretty-printer uses functions defined in Leon itself.
  * If not pretty printing function is defined, return the default value instead
  */
class SelfPrettyPrinter extends PrettyPrinterFinder[Lambda, Lambda] { top =>
  implicit val section = leon.utils.DebugSectionEvaluation
  /* Functions whose name does not need to end with `tostring` or which can be abstract, i.e. which may contain a choose construct.*/
  protected var allowedFunctions = Set[FunDef]()
  /* Functions totally excluded from the set of pretty-printer candidates */
  protected var excluded = Set[FunDef]()
  /** Functions whose name does not need to end with `tostring` or which can be abstract, i.e. which may contain a choose construct.*/
  def allowFunction(fd: FunDef) = { allowedFunctions += fd; this }
  /** Functions totally excluded from the set of pretty-printer candidates*/
  def excludeFunctions(fds: Set[FunDef]) = { excluded ++= fds; this }
  /** Function totally excluded from the set of pretty-printer candidates*/
  def excludeFunction(fd: FunDef) = { excluded += fd; this }

  protected def isExcluded(fd: FunDef): Boolean = top.excluded(fd)
  protected def isAllowed(fd: FunDef): Boolean = top.allowedFunctions(fd)
  
  override def getPrintersForType(t: TypeTree)(implicit ctx: LeonContext, program: Program): Option[Stream[Lambda]] = t match {
    case FunctionType(Seq(StringType), StringType) => // Should have one argument.
      val s = FreshIdentifier("s", StringType) // verify the type
      Some(Stream(Lambda(Seq(ValDef(s)), Variable(s))) ++ super.getPrintersForType(t).getOrElse(Stream.empty) )
    case _ => super.getPrintersForType(t)
  }
  
  /** From a list of lambdas used for pretty-printing the arguments of a function, builds the lambda for the function itself. */
  def buildLambda(inputType: TypeTree, fd: FunDef, slu: Stream[List[Lambda]]): Stream[Lambda] = {
    for(lambdas <- slu) yield {
      val x = FreshIdentifier("x", inputType) // verify the type
      Lambda(Seq(ValDef(x)), functionInvocation(fd, Variable(x)::lambdas))
    }
  }
  
  object withPossibleParameters extends PrettyPrinterFinder[(Lambda, List[Identifier]), (Expr, List[Identifier])]  {
    protected def isExcluded(fd: FunDef): Boolean = top.excluded(fd)
    protected def isAllowed(fd: FunDef): Boolean = top.allowedFunctions(fd)
    
    /** If the returned identifiers are instantiated, each lambda becomes a pretty-printer.
      * This allows to make use of mkString functions such as for maps */
    def prettyPrintersForTypes(inputType: TypeTree)(implicit ctx: LeonContext, program: Program) = {
      program.definedFunctions.toStream flatMap { fd =>
        if(isCandidate(fd)) prettyPrinterFromCandidate(fd, inputType) else Stream.Empty
      }
    }
    
    /** Adds the possibility to have holes in expression */
    override def getPrintersForType(t: TypeTree)(implicit ctx: LeonContext, program: Program) = t match {
      case FunctionType(Seq(StringType), StringType) => // Should have one argument.
        val s = FreshIdentifier("s", StringType) // verify the type
        Some(Stream((Lambda(Seq(ValDef(s)), Variable(s)), List())) ++ super.getPrintersForType(t).getOrElse(Stream.empty) )
      case StringType => 
        val const = FreshIdentifier("const", StringType)
        Some(Stream((Variable(const), List(const))))
      case _ => super.getPrintersForType(t)
    }
    
    /** From a list of expressions gathered for the parameters of the function definition, builds the lambda. */
    def buildLambda(inputType: TypeTree, fd: FunDef, slu: Stream[List[(Expr, List[Identifier])]]) = {
      for(lambdas <- slu) yield {
        val (args, ids) = lambdas.unzip
        val all_ids = ids.flatten
        val x = FreshIdentifier("x", inputType) // verify the type
        (Lambda(Seq(ValDef(x)), functionInvocation(fd, Variable(x)::args)), all_ids)
      }
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
          case e: ContextualEvaluator#EvalError =>
            ctx.reporter.debug("Error "  + e.msg)
            orElse
        }
    }
  }
}
