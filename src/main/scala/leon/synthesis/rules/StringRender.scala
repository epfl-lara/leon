/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._
import purescala.Definitions._
import leon.utils.DebugSectionSynthesis
import leon.purescala.Common.{Identifier, FreshIdentifier}
import leon.purescala.Definitions.FunDef
import leon.utils.IncrementalMap
import leon.purescala.Definitions.FunDef
import leon.purescala.Definitions.ValDef
import scala.collection.mutable.ListBuffer
import leon.purescala.ExprOps
import leon.evaluators.Evaluator
import leon.evaluators.DefaultEvaluator
import leon.solvers.Model
import leon.solvers.ModelBuilder
import leon.solvers.string.StringSolver
import scala.annotation.tailrec


/** A template generator for a given type tree. 
  * Extend this class using a concrete type tree,
  * Then use the apply method to get a hole which can be a placeholder for holes in the template.
  * Each call to the ``.instantiate` method of the subsequent Template will provide different instances at each position of the hole.
  */
abstract class TypedTemplateGenerator(t: TypeTree) {
  /** Provides a hole which can be */
  def apply(f: Expr => Expr): TemplateGenerator = {
    val id = FreshIdentifier("ConstToInstantiate", t, true)
    new TemplateGenerator(f(Variable(id)), id, t)
  }
  class TemplateGenerator(template: Expr, varId: Identifier, t: TypeTree) {
    private val optimizationVars = ListBuffer[Identifier]()
    private def Const: Variable = {
      val res = FreshIdentifier("const", t, true)
      optimizationVars += res
      Variable(res)
    }
    def instantiate = {
      ExprOps.postMap({
        case Variable(id) if id == varId => Some(Const)
        case _ => None
      })(template)
    }
  }
}

/**
 * @author Mikael
 */
case object StringRender extends Rule("StringRender") {
  
  var _defaultTypeToString: Option[Map[TypeTree, FunDef]] = None
  
  def defaultMapTypeToString()(implicit hctx: SearchContext): Map[TypeTree, FunDef] = {
    _defaultTypeToString.getOrElse{
      // Updates the cache with the functions converting standard types to string.
      val res = (hctx.program.library.StrOps.toSeq.flatMap { StrOps => 
        StrOps.defs.collect{ case d: FunDef if d.params.length == 1 && d.returnType == StringType => d.params.head.getType -> d }
      }).toMap
      _defaultTypeToString = Some(res)
      res
    }
  }
  
  /** Returns a toString function converter if it has been defined. */
  class WithFunDefConverter(implicit hctx: SearchContext) {
    def unapply(tpe: TypeTree): Option[FunDef] = {
      _defaultTypeToString.flatMap(_.get(tpe))
    }
  }
  
  val e: AbstractClassType = null
  
  /** Returns a seq of expressions such as `x + y + "1" + y + "2" + z` associated to an expected result string `"1, 2"`.
    * We use these equations so that we can find the values of the constants x, y, z and so on.
    * This uses a custom evaluator which does not concatenate string but reminds the calculation.
    */
  def createProblems(inlineFunc: Seq[FunDef], inlineExpr: Expr, examples: ExamplesBank): Seq[(Expr, String)] = ???
  
  /** For each solution to the problem such as `x + "1" + y + j + "2" + z = 1, 2`, outputs all possible assignments if they exist. */
  def solveProblems(problems: Seq[(Expr, String)]): Seq[Map[Identifier, String]] = ???
  
  
  /// Disambiguation: Enumerate different solutions, augment the size of examples by 1, and check discrepancies.
  
  /** Returns a stream of expressions consistent with the specifications. Tail-recursive method*/
  def solve(ADTToString: Map[TypeTree, FunDef], inputs: Seq[(Identifier, TypeTree)], inlineFuns: Seq[FunDef], inlineExpr: Expr, examples: ExamplesBank): Stream[(FunDef, Expr)] = {
    val inputTypeWithoutToStringFunction = inputs.collectFirst{ case (input, tpe: AbstractClassType) if
      WithStringconverter.unapply(tpe).isEmpty &&
      ADTToString.contains(tpe) =>
        (input, tpe)
    }
    
    inputTypeWithoutToStringFunction match {
      case Some((input, tpe)) =>
        val inductOn = FreshIdentifier(input.name, input.getType, true)
        val fd = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true),
            Nil, ValDef(inductOn) :: Nil, StringType) // Empty function.
        solve(ADTToString + (tpe -> fd), inputs, inlineFuns ++ Seq(fd), inlineExpr, examples) // Tail recursion.
      case None =>
        // Now all types have a corresponding toString function, even if it is empty for now.
        
        
        
        Stream.Empty
    }
  }
  import StringSolver.{StringFormToken, StringForm, Problem => SProblem, Equation}
  
  /** Converts an expression to a stringForm, suitable for StringSolver */
  def toStringForm(e: Expr, acc: List[StringFormToken] = Nil): Option[StringForm] = e match {
    case StringLiteral(s) => Some(Left(s)::acc)
    case Variable(id) => Some(Right(id)::acc)
    case StringConcat(lhs, rhs) => 
      toStringForm(rhs, acc).flatMap(toStringForm(lhs, _))
    case _ => None
  }
  
  /** Returns the string associated to the expression if it is computable */
  def toStringLiteral(e: Expr): Option[String] = e match {
    case StringLiteral(s) => Some(s)
    case StringConcat(lhs, rhs) => toStringLiteral(lhs).flatMap(k => toStringLiteral(rhs).map(l => k + l))
    case _ => None
  }
  
  /** Returns a stream of assignments compatible with input/output examples */
  def findAssignments(ctx: LeonContext, p: Program, inputs: Seq[Identifier], examples: ExamplesBank, template: Expr): Stream[Map[Identifier, String]] = {
    //new Evaluator()
    val e = new DefaultEvaluator(ctx, p)
    
    var invalid = false
    
    @tailrec def gatherEquations(s: List[InOutExample], acc: ListBuffer[Equation] = ListBuffer()): Option[SProblem] = s match {
      case Nil => Some(acc.toList)
      case InOutExample(in, rhExpr)::q =>
        if(rhExpr.length == 1) {
          val model = new ModelBuilder
          model ++= inputs.zip(in)
          e.eval(template, model.result()).result match {
            case None => None
            case Some(sfExpr) =>
              val sf = toStringForm(sfExpr)
              val rhs = toStringLiteral(rhExpr.head)
              if(sf.isEmpty || rhs.isEmpty) None
              else gatherEquations(q, acc += ((sf.get, rhs.get)))
          }
        } else None
    }
    gatherEquations(examples.valids.collect{ case io:InOutExample => io }.toList) match {
      case Some(problem) => StringSolver.solve(problem)
      case None => Stream.empty
    }
  }
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.xs match {
      case List(IsTyped(v, StringType)) =>
        val description = "Creates a standard string conversion function"
        
        val defaultToStringFunctions = defaultMapTypeToString()
        
        val examplesFinder = new ExamplesFinder(hctx.context, hctx.program)
        val examples = examplesFinder.extractFromProblem(p)
        
        /*  Possible strategies.
          * If data structure is recursive on at least one variable (see how Induction works)
          * then
          *   - Inserts a new rec function deconstructing it and put it into the available preconditions to use.
          * If the input is constant
          *   - just a variable to compute a constant.
          * If there are several variables
          *   - All possible ways of linearly unbuilding the structure.
          *   - Or maybe try to infer top-bottom the order of variables from examples?
          * if a variable is a primitive
          *   - Introduce an ordered string containing the content.
          *   
          * Once we have a skeleton, we run it on examples given and solve it.
          * If there are multiple solutions, we generate one deeper example and ask the user which one should be better.
          */
        
        object StringTemplateGenerator extends TypedTemplateGenerator(StringType)
        val booleanTemplate = (a: Identifier) => StringTemplateGenerator(Hole => IfExpr(Variable(a), Hole, Hole))
        
        /* All input variables which are inductive in the post condition, along with their abstract data type. */
        p.as match {
          case List(IsTyped(a, tpe@WithStringconverter(converter))) => // Standard conversions if they work.
            
            val ruleInstantiations = ListBuffer[RuleInstantiation]()
            if(tpe == BooleanType) {
              ruleInstantiations += RuleInstantiation("Boolean split render") {
                val template = booleanTemplate(a).instantiate
                val solutions = findAssignments(hctx.context, hctx.program, p.as, examples, template)
                if(solutions.isEmpty) RuleFailed() else {
                  RuleClosed(solutions.map((assignment: Map[Identifier, String]) => {
                    Solution(pre=p.pc, defs=Set(), term=ExprOps.replaceFromIDs(assignment.mapValues(StringLiteral), template))
                  }))
                }
              }
            }
            
            ruleInstantiations += RuleInstantiation("String conversion with pre and post") {
                val template = StringTemplateGenerator(Hole => StringConcat(StringConcat(Hole, converter(Variable(a))), Hole)).instantiate
                val solutions = findAssignments(hctx.context, hctx.program, p.as, examples, template)
                if(solutions.isEmpty) RuleFailed() else {
                  RuleClosed(solutions.map((assignment: Map[Identifier, String]) => {
                    Solution(pre=p.pc, defs=Set(), term=ExprOps.replaceFromIDs(assignment.mapValues(StringLiteral), template))
                  }))
                }
              }
            ruleInstantiations.toList
          case _ =>
            Nil
        }
        
      case _ => Nil
    }
  }
}