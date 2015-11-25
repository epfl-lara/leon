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
import leon.programsets.{UnionProgramSet, DirectProgramSet, JoinProgramSet}


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
  def toStringForm(e: Expr, acc: List[StringFormToken] = Nil)(implicit hctx: SearchContext): Option[StringForm] = e match {
    case StringLiteral(s) => 
      Some(Left(s)::acc)
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
  def findAssignments(p: Program, inputs: Seq[Identifier], examples: ExamplesBank, template: Expr)(implicit hctx: SearchContext): Stream[Map[Identifier, String]] = {
    //new Evaluator()
    val e = new StringTracingEvaluator(hctx.context, p)
    
    @tailrec def gatherEquations(s: List[InOutExample], acc: ListBuffer[Equation] = ListBuffer()): Option[SProblem] = s match {
      case Nil => Some(acc.toList)
      case InOutExample(in, rhExpr)::q =>
        if(rhExpr.length == 1) {
          val model = new ModelBuilder
          model ++= inputs.zip(in)
          val modelResult = model.result()
          //ctx.reporter.debug("Going to evaluate this template:" + template)
          val evalResult =  e.eval(template, modelResult)
          evalResult.result match {
            case None =>
              hctx.reporter.debug("Eval = None : ["+template+"] in ["+inputs.zip(in)+"]")
              None
            case Some((sfExpr, abstractSfExpr)) =>
              //ctx.reporter.debug("Eval = ["+sfExpr+"] (from "+abstractSfExpr+")")
              val sf = toStringForm(sfExpr)
              val rhs = toStringLiteral(rhExpr.head)
              if(sf.isEmpty || rhs.isEmpty) {
                hctx.reporter.ifDebug(printer => printer("sf empty or rhs empty ["+sfExpr+"] => ["+sf+"] in ["+rhs+"]"))
                None
              } else gatherEquations(q, acc += ((sf.get, rhs.get)))
          }
        } else {
          hctx.reporter.ifDebug(printer => printer("RHS.length != 1 : ["+rhExpr+"]"))
          None 
        }
    }
    gatherEquations(examples.valids.collect{ case io:InOutExample => io }.toList) match {
      case Some(problem) =>
        //hctx.reporter.ifDebug(printer => printer("Problem: ["+StringSolver.renderProblem(problem)+"]"))
        StringSolver.solve(problem)
      case None => 
        hctx.reporter.ifDebug(printer => printer("No problem found"))
        Stream.empty
    }
  }
  
  def findSolutions(examples: ExamplesBank, template: Stream[Expr], funDefs: Seq[(FunDef, Stream[Expr])])(implicit hctx: SearchContext, p: Problem): RuleApplication = {
    // Fun is a stream of many function applications.
    val funs= JoinProgramSet.direct(funDefs.map(fbody => fbody._2.map((fbody._1, _))).map(d => DirectProgramSet(d)))
    
    val wholeTemplates = JoinProgramSet.direct(funs, DirectProgramSet(template))
    
    /*val newProgram = DefOps.addFunDefs(hctx.program, funDefs.values, hctx.sctx.functionContext)
      val newExpr = (expr /: funDefs.values) {
        case (e, fd) => LetDef(fd, e)
      }*/
    def computeSolutions(funDefsBodies: Seq[(FunDef, Expr)], template: Expr): Stream[Assignment] = {
      val funDefs = for((funDef, body) <- funDefsBodies) yield  { funDef.body = Some(body); funDef }
      val newProgram = DefOps.addFunDefs(hctx.program, funDefs, hctx.sctx.functionContext)
      findAssignments(newProgram, p.as, examples, template)
    }
    
    val tagged_solutions =
      for{(funDefs, template) <- wholeTemplates.programs} yield computeSolutions(funDefs, template).map((funDefs, template, _))
    
    solutionStreamToRuleApplication(p, leon.utils.StreamUtils.interleave(tagged_solutions))
  }
  
  def solutionStreamToRuleApplication(p: Problem, solutions: Stream[(Seq[(FunDef, Expr)], Expr, Assignment)]): RuleApplication = {
    if(solutions.isEmpty) RuleFailed() else {
      RuleClosed(
          for((funDefsBodies, singleTemplate, assignment) <- solutions) yield {
            val template = (singleTemplate /: funDefsBodies) {
              case (e, (fd, body)) =>
                fd.body = Some(body)
                LetDef(fd, e)
            }
            val term = ExprOps.simplifyString(ExprOps.replaceFromIDs(assignment.mapValues(StringLiteral), template))
            Solution(pre=p.pc, defs=Set(), term=term)
          })
    }
  }
  
  object StringTemplateGenerator extends TypedTemplateGenerator(StringType)
  
  case class DependentType(caseClassParent: Option[TypeTree], typeToConvert: TypeTree)
  
  
  /** Creates an empty function definition for the dependent type */
  def createEmptyFunDef(tpe: DependentType)(implicit hctx: SearchContext): FunDef = {
    val funName2 = tpe.caseClassParent match {
      case None => tpe.typeToConvert.asString(hctx.context) + "ToString" 
      case Some(t) => tpe.typeToConvert.asString(hctx.context)+"In"+t.asString(hctx.context) + "ToString" 
    }
    val funName3 = funName2.replace("]","").replace("[","")
    val funName = funName3(0).toLower + funName3.substring(1) 
    val funId = FreshIdentifier(funName, alwaysShowUniqueID = true)
    val argId= FreshIdentifier(tpe.typeToConvert.asString(hctx.context).toLowerCase()(0).toString, tpe.typeToConvert)
    val fd = new FunDef(funId, Nil, ValDef(argId) :: Nil, StringType) // Empty function.
    fd
  }
  
  /** Pre-updates of the function definition */
  def preUpdateFunDefBody(tpe: DependentType, fd: FunDef, assignments: Map[DependentType, (FunDef, Stream[Expr])]): Map[DependentType, (FunDef, Stream[Expr])] = {
    assignments.get(tpe) match {
      case None => assignments + (tpe -> ((fd, Stream.Empty)))
      case Some(_) => assignments
    }
  }
  
  /** Returns a (possibly recursive) template which can render the inputs in their order.
    * Returns an expression and path-dependent pretty printers which can be used.
    * 
    * @param inputs The list of inputs. Make sure each identifier is typed.
    **/
  def createFunDefsTemplates(
      currentCaseClassParent: Option[TypeTree],
      adtToString: Map[DependentType, (FunDef, Stream[Expr])],
      inputs: Seq[Identifier])(implicit hctx: SearchContext): (Stream[Expr], Map[DependentType, (FunDef, Stream[Expr])]) = {
    
    /* Returns a list of expressions converting the list of inputs to string.
     * Holes should be inserted before, after and in-between for solving concatenation.
     * @return Along with the list, an updated function definitions to transform (parent-dependent) types to strings */
    @tailrec def gatherInputs(
        currentCaseClassParent: Option[TypeTree],
        assignments1: Map[DependentType, (FunDef, Stream[Expr])],
        inputs: List[Identifier],
        result: ListBuffer[Stream[Expr]] = ListBuffer()): (List[Stream[Expr]], Map[DependentType, (FunDef, Stream[Expr])]) = inputs match {
      case Nil => (result.toList, assignments1)
      case input::q => 
        val dependentType = DependentType(currentCaseClassParent, input.getType)
        assignments1.get(dependentType) match {
        case Some(fd) =>
          // TODO : Maybe find other functions.
          gatherInputs(currentCaseClassParent, assignments1, q, result += Stream(functionInvocation(fd._1, Seq(Variable(input)))))
        case None => // No function can render the current type.
          input.getType match {
            case StringType =>
              gatherInputs(currentCaseClassParent, assignments1, q, result += Stream(Variable(input)))
            case BooleanType =>
              // Special case. But might be overkill.
              // It should be possible to have generic conversion instead, else it needs two examples, which might be cu
              // gatherInputs(currentCaseClassParent, assignments1, q, result += booleanTemplate(input).instantiate)
              // OR
              gatherInputs(currentCaseClassParent, assignments1, q, result += Stream(BooleanToString(Variable(input)), booleanTemplate(input).instantiate))
            case WithStringconverter(converter) => // Base case
              gatherInputs(currentCaseClassParent, assignments1, q, result += Stream(converter(Variable(input))))
            case t: ClassType =>
              // Create the empty function body and updates the assignments parts.
              val fd = createEmptyFunDef(dependentType)
              val assignments2 = preUpdateFunDefBody(dependentType, fd, assignments1) // Inserts the FunDef in the assignments so that it can already be used.
              t.root match {
                case act@AbstractClassType(acd@AbstractClassDef(id, tparams, parent), tps) =>
                  // Create a complete FunDef body with pattern matching
                  val (assignments3, cases) = ((assignments2, ListBuffer[Stream[MatchCase]]()) /: act.knownCCDescendants) {
                    case ((assignments2tmp, acc), CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2)) =>
                      val typeMap = tparams.zip(tparams2).toMap
                      def resolveType(t: TypeTree): TypeTree = TypeOps.instantiateType(t, typeMap)
                      val fields = ccd.fields.map(vd => ( TypeOps.instantiateType(vd, typeMap).id ))
                      val pattern = CaseClassPattern(None, ccd.typed(tparams2), fields.map(k => WildcardPattern(Some(k))))
                      val (rhs, assignments2tmp2) = createFunDefsTemplates(Some(t), assignments2tmp, fields) // Invoke functions for each of the fields.
                      (assignments2tmp2, acc += rhs.map(MatchCase(pattern, None, _)))
                    case ((adtToString, acc), e) => hctx.reporter.fatalError("Could not handle this class definition for string rendering " + e)
                  }
                  val recombine = (cases: Seq[MatchCase]) => MatchExpr(Variable(fd.params(0).id), cases)
                  val allMatchExprs = JoinProgramSet(cases.map(DirectProgramSet(_)), recombine).programs
                  val assignments4 = assignments3 + (dependentType -> (fd, allMatchExprs))
                  gatherInputs(currentCaseClassParent, assignments4, q, result += Stream(functionInvocation(fd, Seq(Variable(input)))))
                case cct@CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2) =>
                  val typeMap = tparams.zip(tparams2).toMap
                  def resolveType(t: TypeTree): TypeTree = TypeOps.instantiateType(t, typeMap)
                  val fields = ccd.fields.map(vd => TypeOps.instantiateType(vd, typeMap).id)
                  val pattern = CaseClassPattern(None, ccd.typed(tparams2), fields.map(k => WildcardPattern(Some(k))))
                  val (rhs, assignments3) = createFunDefsTemplates(Some(t), assignments2, fields) // Invoke functions for each of the fields.
                  
                  val recombine = (cases: Seq[MatchCase]) => MatchExpr(Variable(fd.params(0).id), cases)
                  val cases = rhs.map(MatchCase(pattern, None, _))
                  val allMatchExprs = cases.map(acase => recombine(Seq(acase)))
                  val assignments4 = assignments3 + (dependentType -> (fd, allMatchExprs))
                  gatherInputs(currentCaseClassParent, assignments4, q, result += Stream(functionInvocation(fd, Seq(Variable(input)))))
              }
            case TypeParameter(t) =>
              hctx.reporter.fatalError("Could not handle type parameter for string rendering " + t)
            case tpe => 
              hctx.reporter.fatalError("Could not handle class type for string rendering " + tpe)
          }
      }
    }
    val (exprs, assignments) = gatherInputs(currentCaseClassParent, adtToString, inputs.toList)
    /** Add post, pre and in-between holes, and returns a single expr along with the new assignments. */
    
    val template: Stream[Expr] = exprs match {
      case Nil =>
        Stream(StringTemplateGenerator(Hole => Hole).instantiate)
      case exprList =>
        JoinProgramSet(exprList.map(DirectProgramSet(_)), (exprs: Seq[Expr]) =>
            StringTemplateGenerator(Hole => {
              StringConcat((StringConcat(Hole, exprs.head) /: exprs.tail) {
                case (finalExpr, expr) => StringConcat(StringConcat(finalExpr, Hole), expr)
              }, Hole)
            }).instantiate
        ).programs
    }
    (template, assignments)
  }
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    hctx.reporter.debug("StringRender:Output variables="+p.xs+", their types="+p.xs.map(_.getType))
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
          val (expr, funDefs) = createFunDefsTemplates(None, Map(), p.as)
          
          val toDebug: String = (("\nInferred functions:" /: funDefs)( (t, s) =>
                t + "\n" + s.toString
              ))
          hctx.reporter.ifDebug(printer => printer("Inferred expression:\n" + expr + toDebug))
          
          /*val newProgram = DefOps.addFunDefs(hctx.program, funDefs.values, hctx.sctx.functionContext)
          val newExpr = (expr /: funDefs.values) {
            case (e, fd) => LetDef(fd, e)
          }*/
          findSolutions(examples, expr, funDefs.values.toSeq)
        }
        
        ruleInstantiations.toList
        
      case _ => Nil
    }
  }
}