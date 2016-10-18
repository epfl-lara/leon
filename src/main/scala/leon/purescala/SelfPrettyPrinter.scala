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
  
  /** How to fill the arguments for user-defined pretty-printers */
  def getPrintersForType(t: TypeTree, topLevel: TypeTree)(implicit ctx: LeonContext, program: Program): Option[Stream[U]] = t match {
    case FunctionType(Seq(in), StringType) if in != topLevel => // Should have one argument.
      Some(prettyPrintersForType(in))
    case _ => None
  }
  
  // To Implement
  def buildLambda(inputType: TypeTree, fd: FunDef, slu: Stream[List[U]]): Stream[T]
  
  def prettyPrinterFromCandidate(fd: FunDef, inputType: TypeTree)(implicit ctx: LeonContext, program: Program): Stream[T] = {
    TypeOps.instantiation_>:(fd.params.head.getType, inputType) match {
      case Some(genericTypeMap) =>
        //println("Found a mapping for inputType = " + inputType + " " + fd)
        def gatherPrettyPrinters(funIds: List[Identifier], acc: ListBuffer[Stream[U]] = ListBuffer[Stream[U]]()): Option[Stream[List[U]]] = funIds match {
          case Nil => Some(StreamUtils.cartesianProduct(acc.toList))
          case funId::tail => // For each function, find an expression which could be provided if it exists.
            getPrintersForType(funId.getType, inputType) match {
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
  /** Function whose name does not need to end with `tostring` or which can be abstract, i.e. which may contain a choose construct.*/
  def allowFunction(fd: FunDef) = { allowedFunctions += fd; this }
  /** Functions whose name does not need to end with `tostring` or which can be abstract, i.e. which may contain a choose construct.*/
  def allowFunctions(fds: Set[FunDef]) = { allowedFunctions ++= fds; this }
  /** Functions totally excluded from the set of pretty-printer candidates*/
  def excludeFunctions(fds: Set[FunDef]) = { excluded ++= fds; this }
  /** Function totally excluded from the set of pretty-printer candidates*/
  def excludeFunction(fd: FunDef) = { excluded += fd; this }

  protected def isExcluded(fd: FunDef): Boolean = top.excluded(fd)
  protected def isAllowed(fd: FunDef): Boolean = top.allowedFunctions(fd)
  
  /** How to fill the arguments for user-defined pretty-printers */
  override def getPrintersForType(t: TypeTree, underlying: TypeTree)(implicit ctx: LeonContext, program: Program): Option[Stream[Lambda]] = t match {
    case FunctionType(Seq(StringType), StringType) => // Should have one argument.
      val s = FreshIdentifier("s", StringType) // verify the type
      Some(Stream(Lambda(Seq(ValDef(s)), Variable(s))) ++ super.getPrintersForType(t, underlying).getOrElse(Stream.empty) )
    case _ => super.getPrintersForType(t, underlying)
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
      (program.definedFunctions.toStream flatMap { fd =>
        if(isCandidate(fd)) prettyPrinterFromCandidate(fd, inputType) else Stream.Empty
      }) #::: {
        inputType match {
          case Int32Type =>
            val i = FreshIdentifier("i", Int32Type)
            Stream((Lambda(Seq(ValDef(i)), Int32ToString(Variable(i))), List[Identifier]()))
          case IntegerType =>
            val i = FreshIdentifier("i", IntegerType)
            Stream((Lambda(Seq(ValDef(i)), IntegerToString(Variable(i))), List[Identifier]()))
          case StringType =>
            val i = FreshIdentifier("i", StringType)
            Stream((Lambda(Seq(ValDef(i)), Variable(i)), List[Identifier]()))
          case BooleanType =>
            val i = FreshIdentifier("i", BooleanType)
            Stream((Lambda(Seq(ValDef(i)), BooleanToString(Variable(i))), List[Identifier]()))
          case _ => Stream.empty
        }
      }
    }
    import leon.purescala.Extractors._
    
    /** How to fill the arguments for user-defined pretty-printers */
    override def getPrintersForType(t: TypeTree, underlying: TypeTree)(implicit ctx: LeonContext, program: Program) = t match {
      case FunctionType(Seq(StringType), StringType) => // Should have one argument.
        val s = FreshIdentifier("s", StringType) // verify the type
        Some(Stream((Lambda(Seq(ValDef(s)), Variable(s)), List())) ++ super.getPrintersForType(t, underlying).getOrElse(Stream.empty) )
      case FunctionType(Seq(t@ WithStringconverter(converter)), StringType) => // Should have one argument.
        val s = FreshIdentifier("s", t) // verify the type
        Some(Stream((Lambda(Seq(ValDef(s)), converter(Variable(s))), List())) ++ super.getPrintersForType(t, underlying).getOrElse(Stream.empty) )
      case StringType => 
        val const = FreshIdentifier("const", StringType, true)
        Some(Stream((Variable(const), List(const))))
      case TupleType(targs) =>
        def convertPrinters(ts: Seq[TypeTree]): Option[Seq[Stream[(Expressions.Expr, List[Common.Identifier])]]] = {
          ts match {
            case Nil => Some(Seq())
            case t::tail =>
              getPrintersForType(t, underlying).flatMap(current =>
                convertPrinters(tail).map(remaining =>
                  current +: remaining))
          }
        }
        convertPrinters(targs) match {
          case None => None
          case Some(t) =>
            val regrouped = leon.utils.StreamUtils.cartesianProduct(t)
            val result = regrouped.map{lst =>
              val identifiers = lst.flatMap(_._2)
              val lambdas = lst.collect{ case (l: Lambda, _) => l}
              val valdefs = lambdas.flatMap(_.args)
              val bodies = lst.map{ case (l: Lambda, _) => l.body case (e, _) => e }
              if(valdefs.isEmpty) {
                (Tuple(bodies), identifiers)
              } else {
                (Lambda(valdefs, Tuple(bodies)), identifiers)
              }
            }
            Some(result)
        }
      case _ => super.getPrintersForType(t, underlying)
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
