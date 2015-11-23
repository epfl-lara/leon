/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.TypeOps
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
import leon.evaluators.StringTracingEvaluator
import leon.solvers.Model
import leon.solvers.ModelBuilder
import leon.solvers.string.StringSolver
import scala.annotation.tailrec
import leon.purescala.DefOps


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
  
  val booleanTemplate = (a: Identifier) => StringTemplateGenerator(Hole => IfExpr(Variable(a), Hole, Hole))
  
  /** Returns a seq of expressions such as `x + y + "1" + y + "2" + z` associated to an expected result string `"1, 2"`.
    * We use these equations so that we can find the values of the constants x, y, z and so on.
    * This uses a custom evaluator which does not concatenate string but reminds the calculation.
    */
  def createProblems(inlineFunc: Seq[FunDef], inlineExpr: Expr, examples: ExamplesBank): Seq[(Expr, String)] = ???
  
  /** For each solution to the problem such as `x + "1" + y + j + "2" + z = 1, 2`, outputs all possible assignments if they exist. */
  def solveProblems(problems: Seq[(Expr, String)]): Seq[Map[Identifier, String]] = ???
  
  
  /// Disambiguation: Enumerate different solutions, augment the size of examples by 1, and check discrepancies.
  
  
    
    
    
    
    /*val inputTypeWithoutToStringFunction = inputs.collectFirst{ case (input, tpe: AbstractClassType) if
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
    }*/
  import StringSolver.{StringFormToken, StringForm, Problem => SProblem, Equation, Assignment}
  
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
    val e = new StringTracingEvaluator(ctx, p)
    
    var invalid = false
    
    @tailrec def gatherEquations(s: List[InOutExample], acc: ListBuffer[Equation] = ListBuffer()): Option[SProblem] = s match {
      case Nil => Some(acc.toList)
      case InOutExample(in, rhExpr)::q =>
        if(rhExpr.length == 1) {
          val model = new ModelBuilder
          model ++= inputs.zip(in)
          val modelResult = model.result()
          val evalResult =  e.eval(template, modelResult)
          evalResult.result match {
            case None =>
              ctx.reporter.ifDebug(printer => printer("Eval = None : ["+template+"] in ["+inputs.zip(in)+"]"))
              None
            case Some((sfExpr, _)) =>
              val sf = toStringForm(sfExpr)
              val rhs = toStringLiteral(rhExpr.head)
              if(sf.isEmpty || rhs.isEmpty) {
                ctx.reporter.ifDebug(printer => printer("sf empty or rhs empty ["+sfExpr+"] => ["+sf+"] in ["+rhs+"]"))
                None
              } else gatherEquations(q, acc += ((sf.get, rhs.get)))
          }
        } else {
          ctx.reporter.ifDebug(printer => printer("RHS.length != 1 : ["+rhExpr+"]"))
          None 
        }
    }
    gatherEquations(examples.valids.collect{ case io:InOutExample => io }.toList) match {
      case Some(problem) =>
        ctx.reporter.ifDebug(printer => printer("Problem: ["+problem+"]"))
        StringSolver.solve(problem)
      case None => 
        ctx.reporter.ifDebug(printer => printer("No problem found"))
        Stream.empty
    }
  }
  
  def findSolutions(examples: ExamplesBank, program: Program, template: Expr)(implicit hctx: SearchContext, p: Problem): RuleApplication = {
    val solutions = findAssignments(hctx.context, program, p.as, examples, template)
    hctx.reporter.ifDebug(printer => printer("Solutions: ["+solutions.toList+"]"))
    
    solutionStreamToRuleApplication(p, template, solutions)
  }
  
  def solutionStreamToRuleApplication(p: Problem, template: Expr, solutions: Stream[Assignment]): RuleApplication = {
    if(solutions.isEmpty) RuleFailed() else {
      RuleClosed(solutions.map((assignment: Map[Identifier, String]) => {
        val term = ExprOps.simplifyString(ExprOps.replaceFromIDs(assignment.mapValues(StringLiteral), template))
        Solution(pre=p.pc, defs=Set(), term=term)
      }))
    }
  }
  
  object StringTemplateGenerator extends TypedTemplateGenerator(StringType)
  
  case class DependentType(caseClassParent: Option[TypeTree], typeToConvert: TypeTree)
  
  
  /** Creates an empty function definition for the dependent type */
  def createEmptyFunDef(tpe: DependentType)(implicit hctx: SearchContext): FunDef = {
    val funName2 = tpe.caseClassParent match {
      case None => tpe.typeToConvert.asString(hctx.context)
      case Some(t) => tpe.typeToConvert.asString(hctx.context)+"In"+t.asString(hctx.context) + "ToString" 
    }
    val funName = funName2.replace("]","").replace("[","")
    val funId = FreshIdentifier(funName, alwaysShowUniqueID = true)
    val argId= FreshIdentifier(tpe.typeToConvert.asString(hctx.context).toLowerCase()(0).toString, tpe.typeToConvert)
    val fd = new FunDef(funId, Nil, ValDef(argId) :: Nil, StringType) // Empty function.
    fd
  }
  
  /** Pre-updates of the function definition */
  def preUpdateFunDefBody(tpe: DependentType, fd: FunDef, assignments: Map[DependentType, FunDef]): Map[DependentType, FunDef] = {
    assignments.get(tpe) match {
      case None => assignments + (tpe -> fd)
      case Some(_) => assignments
    }
  }
  
  /** Returns a (possibly recursive) template which can render the inputs in their order.
    * Returns an expression and path-dependent pretty printers which can be used.
    **/
  def createFunDefsTemplates(
      currentCaseClassParent: Option[TypeTree],
      adtToString: Map[DependentType, FunDef],
      inputs: Seq[(Identifier, TypeTree)])(implicit hctx: SearchContext): (Expr, Map[DependentType, FunDef]) = {
    
    /* Returns a list of expressions converting the list of inputs to string.
     * Holes should be inserted before, after and in-between for solving concatenation.
     * @return Along with the list, an updated function definitions to transform (parent-dependent) types to strings */
    @tailrec def gatherInputs(
        currentCaseClassParent: Option[TypeTree],
        assignments1: Map[DependentType, FunDef],
        inputs: List[(Identifier, TypeTree)],
        result: ListBuffer[Expr] = ListBuffer()): (List[Expr], Map[DependentType, FunDef]) = inputs match {
      case Nil => (result.toList, assignments1)
      case (input, tpe)::q => 
        val dependentType = DependentType(currentCaseClassParent, tpe)
        assignments1.get(dependentType) match {
        case Some(fd) =>
          hctx.reporter.debug("found a function definition " + fd)
          
          gatherInputs(currentCaseClassParent, assignments1, q, result += functionInvocation(fd, Seq(Variable(input))))
        case None => // No function can render the current type.
          tpe match {
            case BooleanType => // Special case.
              gatherInputs(currentCaseClassParent, assignments1, q, result += booleanTemplate(input).instantiate)
            case WithStringconverter(converter) => // Base case
              gatherInputs(currentCaseClassParent, assignments1, q, result += converter(Variable(input)))
            case t: ClassType =>
              // Create the empty function body and updates the assignments parts.
              val fd = createEmptyFunDef(dependentType)
              hctx.reporter.debug("Creating a new function for " + dependentType)
              val assignments2 = preUpdateFunDefBody(dependentType, fd, assignments1) // Inserts the FunDef in the assignments so that it can already be used.
              t.root match {
                case act@AbstractClassType(acd@AbstractClassDef(id, tparams, parent), tps) =>
                  hctx.reporter.debug("preparing cases classes for " + act)
                  // Create a complete FunDef body with pattern matching
                  val (assignments3, cases) = ((assignments2, ListBuffer[MatchCase]()) /: act.knownCCDescendants) {
                    case ((assignments2tmp, acc), CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2)) =>
                      val typeMap = tparams.zip(tparams2).toMap
                      def resolveType(t: TypeTree): TypeTree = TypeOps.instantiateType(t, typeMap) 
                      val fields = ccd.fields.map(vd => ( TypeOps.instantiateType(vd, typeMap).id, resolveType(vd.tpe.get)))
                      val fieldsIds = fields.map(id => FreshIdentifier(id._1.name, id._2))
                      val pattern = CaseClassPattern(None, ccd.typed(tparams2), fieldsIds.map(k => WildcardPattern(Some(k))))
                      val (rhs, assignments2tmp2) = createFunDefsTemplates(Some(t), assignments2tmp, fields) // Invoke functions for each of the fields.
                      (assignments2tmp2, acc += MatchCase(pattern, None, rhs))
                    case ((adtToString, acc), e) => hctx.reporter.fatalError("Could not handle this class definition for string rendering " + e)
                  }
                  fd.body = Some(MatchExpr(Variable(input), cases))
                  gatherInputs(currentCaseClassParent, assignments3, q, result += functionInvocation(fd, Seq(Variable(input))))
                case cct@CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2) =>
                  hctx.reporter.debug("preparing function for " + cct)
                  val typeMap = tparams.zip(tparams2).toMap
                  def resolveType(t: TypeTree): TypeTree = TypeOps.instantiateType(t, typeMap)
                  val fields = ccd.fields.map(vd => (TypeOps.instantiateType(vd, typeMap).id, resolveType(vd.tpe.get)))
                  val fieldsIds = fields.map(id => FreshIdentifier(id._1.name, id._2))
                  val pattern = CaseClassPattern(None, ccd.typed(tparams2), fieldsIds.map(k => WildcardPattern(Some(k))))
                  val (rhs, assignments3) = createFunDefsTemplates(Some(t), assignments2, fields) // Invoke functions for each of the fields.
                  fd.body = Some(MatchExpr(Variable(input), Seq(MatchCase(pattern, None, rhs))))
                  gatherInputs(currentCaseClassParent, assignments3, q, result += functionInvocation(fd, Seq(Variable(input))))
              }
            case TypeParameter(t) =>
              hctx.reporter.fatalError("Could not handle type parameter for string rendering " + t)
            case _ => 
              hctx.reporter.fatalError("Could not handle class type for string rendering " + tpe)
          }
      }
    }
    val (exprs, assignments) = gatherInputs(currentCaseClassParent, adtToString, inputs.toList)
    /** Add post, pre and in-between holes, and returns a single expr along with the new assignments. */
    
    val template = exprs match {
      case Nil =>
        StringTemplateGenerator(Hole => Hole).instantiate
      case exprList =>
        StringTemplateGenerator(Hole => {
          StringConcat((StringConcat(Hole, exprs.head) /: exprs.tail) {
            case (finalExpr, expr) => StringConcat(StringConcat(finalExpr, Hole), expr)
          }, Hole)
        }).instantiate
    }
    (template, assignments)
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
        
        
        
        // Returns expr and funDefs as templates.
        
        val ruleInstantiations = ListBuffer[RuleInstantiation]()
        ruleInstantiations += RuleInstantiation("String conversion") {
          val (expr, funDefs) = createFunDefsTemplates(None, Map(), p.as.map(input => (input, input.getType)))
          
          val toDebug: String = (("\nInferred functions:" /: funDefs)( (t, s) =>
                t + "\n" + s.toString
              ))
          hctx.reporter.ifDebug(printer => printer("Inferred expression:\n" + expr + toDebug))
          
          //val newProgram = DefOps.addFunDefs(hctx.program, funDefs.values, hctx.sctx.functionContext)
          val newExpr = (expr /: funDefs.values) {
            case (e, fd) => LetDef(fd, e)
          }
          findSolutions(examples, hctx.program, newExpr)
        }
        
        ruleInstantiations.toList
        
      case _ => Nil
    }
  }
}