/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

import bonsai.enumerators.MemoizedEnumerator
import leon.evaluators.DefaultEvaluator
import leon.evaluators.StringTracingEvaluator
import leon.synthesis.programsets.DirectProgramSet
import leon.synthesis.programsets.JoinProgramSet
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Common.Identifier
import leon.purescala.DefOps
import leon.purescala.Definitions.FunDef
import leon.purescala.Definitions.FunDef
import leon.purescala.Definitions.ValDef
import leon.purescala.ExprOps
import leon.solvers.Model
import leon.solvers.ModelBuilder
import leon.solvers.string.StringSolver
import leon.utils.DebugSectionSynthesis
import purescala.Constructors._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Expressions._
import purescala.Extractors._
import purescala.TypeOps
import purescala.Types._


/** A template generator for a given type tree. 
  * Extend this class using a concrete type tree,
  * Then use the apply method to get a hole which can be a placeholder for holes in the template.
  * Each call to the ``.instantiate` method of the subsequent Template will provide different instances at each position of the hole.
  */
abstract class TypedTemplateGenerator(t: TypeTree) {
  import StringRender.WithIds
  /** Provides a hole which can be */
  def apply(f: Expr => Expr): TemplateGenerator = {
    val id = FreshIdentifier("ConstToInstantiate", t, true)
    new TemplateGenerator(f(Variable(id)), id, t)
  }
  def nested(f: Expr => WithIds[Expr]): TemplateGenerator = {
    val id = FreshIdentifier("ConstToInstantiate", t, true)
    val res = f(Variable(id))
    new TemplateGenerator(res._1, id, t, res._2)
  }
  class TemplateGenerator(template: Expr, varId: Identifier, t: TypeTree, initialHoles: List[Identifier] = Nil) {
    private val optimizationVars = ListBuffer[Identifier]() ++= initialHoles
    private def Const: Variable = {
      val res = FreshIdentifier("const", t, true)
      optimizationVars += res
      Variable(res)
    }
    private def instantiate: Expr = {
      ExprOps.postMap({
        case Variable(id) if id == varId => Some(Const)
        case _ => None
      })(template)
    }
    def instantiateWithVars: WithIds[Expr] = (instantiate, optimizationVars.toList)
  }
}

/**
 * @author Mikael
 */
case object StringRender extends Rule("StringRender") {
  type WithIds[T] = (T, List[Identifier])
  
  var EDIT_ME = "_edit_me_"
  
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
  
  val booleanTemplate = (a: Expr) => StringTemplateGenerator(Hole => IfExpr(a, Hole, Hole))
  
  /** Returns a seq of expressions such as `x + y + "1" + y + "2" + z` associated to an expected result string `"1, 2"`.
    * We use these equations so that we can find the values of the constants x, y, z and so on.
    * This uses a custom evaluator which does not concatenate string but reminds the calculation.
    */
  def createProblems(inlineFunc: Seq[FunDef], inlineExpr: Expr, examples: ExamplesBank): Seq[(Expr, String)] = ???
  
  /** For each solution to the problem such as `x + "1" + y + j + "2" + z = 1, 2`, outputs all possible assignments if they exist. */
  def solveProblems(problems: Seq[(Expr, String)]): Seq[Map[Identifier, String]] = ???
  
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
  
  /** Returns a stream of assignments compatible with input/output examples for the given template */
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
    gatherEquations((examples.valids ++ examples.invalids).collect{ case io:InOutExample => io }.toList) match {
      case Some(problem) =>
        hctx.reporter.debug("Problem: ["+StringSolver.renderProblem(problem)+"]")
        val res = StringSolver.solve(problem)
        hctx.reporter.debug("Solution found:"+res.nonEmpty)
        res
      case None => 
        hctx.reporter.ifDebug(printer => printer("No problem found"))
        Stream.empty
    }
  }
  
  def findSolutions(examples: ExamplesBank, template: Stream[WithIds[Expr]], funDefs: Seq[(FunDef, Stream[WithIds[Expr]])])(implicit hctx: SearchContext, p: Problem): RuleApplication = {
    // Fun is a stream of many function applications.
    val funs= JoinProgramSet.direct(funDefs.map(fbody => fbody._2.map((fbody._1, _))).map(d => DirectProgramSet(d)))
    
    val wholeTemplates = JoinProgramSet.direct(funs, DirectProgramSet(template))
    
    def computeSolutions(funDefsBodies: Seq[(FunDef, WithIds[Expr])], template: WithIds[Expr]): Stream[Assignment] = {
      val funDefs = for((funDef, body) <- funDefsBodies) yield  { funDef.body = Some(body._1); funDef }
      val newProgram = DefOps.addFunDefs(hctx.program, funDefs, hctx.sctx.functionContext)
      findAssignments(newProgram, p.as, examples, template._1)
    }
    
    val tagged_solutions =
      for{(funDefs, template) <- wholeTemplates.programs} yield computeSolutions(funDefs, template).map((funDefs, template, _))
    
    solutionStreamToRuleApplication(p, leon.utils.StreamUtils.interleave(tagged_solutions))(hctx.program)
  }
  
  /** Find ambiguities not containing _edit_me_ to ask to the user */
  def askQuestion(input: List[Identifier], r: RuleClosed)(implicit c: LeonContext, p: Program): List[disambiguation.Question[StringLiteral]] = {
    //if !s.contains(EDIT_ME)
    val qb = new disambiguation.QuestionBuilder(input, r.solutions, (seq: Seq[Expr], expr: Expr) => expr match {
      case s@StringLiteral(slv) if !slv.contains(EDIT_ME) => Some(s)
      case _ => None
    })
    qb.result()
  }
  
  /** Converts the stream of solutions to a RuleApplication */
  def solutionStreamToRuleApplication(p: Problem, solutions: Stream[(Seq[(FunDef, WithIds[Expr])], WithIds[Expr], Assignment)])(implicit program: Program): RuleApplication = {
    if(solutions.isEmpty) RuleFailed() else {
      RuleClosed(
          for((funDefsBodies, (singleTemplate, ids), assignment) <- solutions) yield {
            val fds = for((fd, (body, ids)) <- funDefsBodies) yield {
              val initMap = ids.map(_ -> StringLiteral(EDIT_ME)).toMap
              fd.body = Some(ExprOps.simplifyString(ExprOps.replaceFromIDs(initMap ++ assignment.mapValues(StringLiteral), body)))
              fd
            }
            val initMap = ids.map(_ -> StringLiteral(EDIT_ME)).toMap
            val term = ExprOps.simplifyString(ExprOps.replaceFromIDs(initMap ++ assignment.mapValues(StringLiteral), singleTemplate))
            val (finalTerm, finalDefs) = makeFunctionsUnique(term, fds.toSet)
            
            Solution(pre=p.pc, defs=finalDefs, term=finalTerm)
          })
    }
  }
  
  /** Crystallizes a solution so that it will not me modified if the body of fds is modified. */
  def makeFunctionsUnique(term: Expr, fds: Set[FunDef])(implicit program: Program): (Expr, Set[FunDef]) = {
    var transformMap = Map[FunDef, FunDef]()
    def mapExpr(body: Expr): Expr = {
      ExprOps.preMap((e: Expr) => e match {
        case FunctionInvocation(TypedFunDef(fd, _), args) if fd != program.library.escape.get => Some(FunctionInvocation(getMapping(fd).typed, args))
        case e => None
      })(body)
    }
    
    def getMapping(fd: FunDef): FunDef = {
      transformMap.getOrElse(fd, {
        val newfunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, fd.returnType) // With empty body
        transformMap += fd -> newfunDef
        newfunDef.body = fd.body.map(mapExpr _)
        newfunDef
      })
    }
    
    (mapExpr(term), fds.map(getMapping _))
  }
  
  
  object StringTemplateGenerator extends TypedTemplateGenerator(StringType)
  
  case class DependentType(caseClassParent: Option[TypeTree], inputName: String, typeToConvert: TypeTree)
  
  object StringSynthesisContext {
    def empty(implicit hctx: SearchContext) = new StringSynthesisContext(None, new StringSynthesisResult(Map(), Set()))
  }
  
  type MapFunctions = Map[DependentType, (FunDef, Stream[WithIds[Expr]])]
  
  /** Result of the current synthesis process */
  class StringSynthesisResult(
      val adtToString: MapFunctions,
      val funNames: Set[String]
  ) {
    def add(d: DependentType, f: FunDef, s: Stream[WithIds[Expr]]): StringSynthesisResult = {
      new StringSynthesisResult(adtToString + (d -> ((f, s))), funNames + f.id.name)
    }
    def freshFunName(s: String): String = {
      if(!funNames(s)) return s
      var i = 1
      var s0 = s
      do {
        i += 1
        s0 = s + i
      } while(funNames(s+i))
      s0
    }
  }
  
  /** Context for the current synthesis process */
  class StringSynthesisContext(
      val currentCaseClassParent: Option[TypeTree],
      val result: StringSynthesisResult
  )(implicit hctx: SearchContext) {
    def add(d: DependentType, f: FunDef, s: Stream[WithIds[Expr]]): StringSynthesisContext = {
      new StringSynthesisContext(currentCaseClassParent, result.add(d, f, s))
    }
    def copy(currentCaseClassParent: Option[TypeTree]=currentCaseClassParent, result: StringSynthesisResult = result): StringSynthesisContext = 
      new StringSynthesisContext(currentCaseClassParent, result)
    def freshFunName(s: String) = result.freshFunName(s)
  }
  
  /** Creates an empty function definition for the dependent type */
  def createEmptyFunDef(ctx: StringSynthesisContext, tpe: DependentType)(implicit hctx: SearchContext): FunDef = {
    def defaultFunName(t: TypeTree) = t match {
      case AbstractClassType(c, d) => c.id.asString(hctx.context)
      case CaseClassType(c, d) => c.id.asString(hctx.context)
      case t => t.asString(hctx.context)
    }
    
    val funName2 = tpe.caseClassParent match {
      case None => defaultFunName(tpe.typeToConvert) + "_" + tpe.inputName + "_s" 
      case Some(t) => defaultFunName(tpe.typeToConvert) + "In"+defaultFunName(t) + "_" + tpe.inputName + "_s" 
    }
    val funName3 = funName2.replaceAll("[^a-zA-Z0-9_]","")
    val funName = funName3(0).toLower + funName3.substring(1) 
    val funId = FreshIdentifier(ctx.freshFunName(funName), alwaysShowUniqueID = true)
    val argId= FreshIdentifier(tpe.typeToConvert.asString(hctx.context).toLowerCase()(0).toString, tpe.typeToConvert)
    val fd = new FunDef(funId, Nil, ValDef(argId) :: Nil, StringType) // Empty function.
    fd
  }
  
  /** Pre-updates of the function definition */
  def preUpdateFunDefBody(tpe: DependentType, fd: FunDef, ctx: StringSynthesisContext): StringSynthesisContext = {
    ctx.result.adtToString.get(tpe) match {
      case None => ctx.add(tpe, fd, Stream.Empty)
      case Some(_) => ctx
    }
  }

  /** Assembles multiple MatchCase to a singleMatchExpr using the function definition fd */
  private val mergeMatchCases = (fd: FunDef) => (cases: Seq[WithIds[MatchCase]]) => (MatchExpr(Variable(fd.params(0).id), cases.map(_._1)), cases.map(_._2).flatten.toList)
  
  /** Returns a (possibly recursive) template which can render the inputs in their order.
    * Returns an expression and path-dependent pretty printers which can be used.
    * 
    * @param inputs The list of inputs. Make sure each identifier is typed.
    **/
  def createFunDefsTemplates(
      ctx: StringSynthesisContext,
      inputs: Seq[Expr])(implicit hctx: SearchContext): (Stream[WithIds[Expr]], StringSynthesisResult) = {
    
    def extractCaseVariants(cct: CaseClassType, ctx: StringSynthesisContext)
      : (Stream[WithIds[MatchCase]], StringSynthesisResult) = cct match {
      case CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2) =>
        val typeMap = tparams.zip(tparams2).toMap
        val fields = ccd.fields.map(vd => TypeOps.instantiateType(vd.id, typeMap) )
        val pattern = CaseClassPattern(None, ccd.typed(tparams2), fields.map(k => WildcardPattern(Some(k))))
        val (rhs, result) = createFunDefsTemplates(ctx.copy(currentCaseClassParent=Some(cct)), fields.map(Variable)) // Invoke functions for each of the fields.
        val newCases = rhs.map(e => (MatchCase(pattern, None, e._1), e._2))
        (newCases, result)
    }
    
    /* Returns a constant pattern matching in which all classes are rendered using their proper name
     * For example:
     * {{{
     * sealed abstract class Thread
     * case class T1() extends Thread()
     * case Class T2() extends Thread()
     * }}}
     * Will yield the following expression:
     * {{{t match {
     *   case T1() => "T1"
     *   case T2() => "T2"
     * }
     * }}}
     * 
     */
    def constantPatternMatching(fd: FunDef, act: AbstractClassType): WithIds[MatchExpr] = {
      val cases = (ListBuffer[WithIds[MatchCase]]() /: act.knownCCDescendants) {
        case (acc, cct@CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2)) =>
          val typeMap = tparams.zip(tparams2).toMap
          val fields = ccd.fields.map(vd => TypeOps.instantiateType(vd.id, typeMap) )
          val pattern = CaseClassPattern(None, ccd.typed(tparams2), fields.map(k => WildcardPattern(Some(k))))
          val rhs = StringLiteral(id.asString)
          MatchCase(pattern, None, rhs)
          acc += ((MatchCase(pattern, None, rhs), Nil))
        case (acc, e) => hctx.reporter.fatalError("Could not handle this class definition for string rendering " + e)
      }
      mergeMatchCases(fd)(cases)
    }
    
    /* Returns a list of expressions converting the list of inputs to string.
     * Each expression is tagged with a list of identifiers, which is the list of variables which need to be found.
     * @return Along with the list, an updated function definitions to transform (parent-dependent) types to strings */
    @tailrec def gatherInputs(
        ctx: StringSynthesisContext,
        inputs: List[Expr],
        result: ListBuffer[Stream[WithIds[Expr]]] = ListBuffer()): (List[Stream[WithIds[Expr]]], StringSynthesisResult) = inputs match {
      case Nil => (result.toList, ctx.result)
      case input::q => 
        val dependentType = DependentType(ctx.currentCaseClassParent, input.asString(hctx.program)(hctx.context), input.getType)
        ctx.result.adtToString.get(dependentType) match {
        case Some(fd) =>
          gatherInputs(ctx, q, result += Stream((functionInvocation(fd._1, Seq(input)), Nil)))
        case None => // No function can render the current type.
          input.getType match {
            case StringType =>
              gatherInputs(ctx, q, result +=
                (Stream((input, Nil),
                        (FunctionInvocation(
                            hctx.program.library.escape.get.typed,
                            Seq(input)): Expr, Nil))))
            case BooleanType =>
              val (bTemplate, vs) = booleanTemplate(input).instantiateWithVars
              gatherInputs(ctx, q, result += Stream((BooleanToString(input), Nil), (bTemplate, vs)))
            case WithStringconverter(converter) => // Base case
              gatherInputs(ctx, q, result += Stream((converter(input), Nil)))
            case t: ClassType =>
              // Create the empty function body and updates the assignments parts.
              val fd = createEmptyFunDef(ctx, dependentType)
              val ctx2 = preUpdateFunDefBody(dependentType, fd, ctx) // Inserts the FunDef in the assignments so that it can already be used.
              t.root match {
                case act@AbstractClassType(acd@AbstractClassDef(id, tparams, parent), tps) =>
                  // Create a complete FunDef body with pattern matching
                  
                  val allKnownDescendantsAreCCAndHaveZeroArgs = act.knownCCDescendants.forall { x => x match {
                    case CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2) => ccd.fields.isEmpty
                    case _ => false
                  }}
                  
                  //TODO: Test other templates not only with Wilcard patterns, but more cases options for non-recursive classes (e.g. Option, Boolean, Finite parameterless case classes.)
                  val (ctx3, cases) = ((ctx2, ListBuffer[Stream[WithIds[MatchCase]]]()) /: act.knownCCDescendants) {
                    case ((ctx22, acc), cct@CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2)) =>
                      val (newCases, result) = extractCaseVariants(cct, ctx22)
                      val ctx23 = ctx22.copy(result = result)
                      (ctx23, acc += newCases)
                    case ((adtToString, acc), e) => hctx.reporter.fatalError("Could not handle this class definition for string rendering " + e)
                  }
                  
                  val allMatchExprsEnd = JoinProgramSet(cases.map(DirectProgramSet(_)), mergeMatchCases(fd)).programs // General pattern match expressions
                  val allMatchExprs = if(allKnownDescendantsAreCCAndHaveZeroArgs) {
                    Stream(constantPatternMatching(fd, act)) ++ allMatchExprsEnd
                  } else allMatchExprsEnd
                  gatherInputs(ctx3.add(dependentType, fd, allMatchExprs), q, result += Stream((functionInvocation(fd, Seq(input)), Nil)))
                case cct@CaseClassType(ccd@CaseClassDef(id, tparams, parent, isCaseObject), tparams2) =>
                  val (newCases, result3) = extractCaseVariants(cct, ctx2)
                  val allMatchExprs = newCases.map(acase => mergeMatchCases(fd)(Seq(acase)))
                  gatherInputs(ctx2.copy(result = result3).add(dependentType, fd, allMatchExprs), q, result += Stream((functionInvocation(fd, Seq(input)), Nil)))
              }
            case TypeParameter(t) =>
              hctx.reporter.fatalError("Could not handle type parameter for string rendering " + t)
            case tpe => 
              hctx.reporter.fatalError("Could not handle class type for string rendering " + tpe)
          }
      }
    }
    var ctx2 = ctx // We gather the functions only once.
    // Flatten tuple types
    val newInputs = inputs.flatMap{ case input =>
      input.getType match {
        case TupleType(bases) =>
          val blength = bases.length
          for(index <- 1 to blength) yield tupleSelect(input, index, blength)
        case _ => List(input)
      }
    }
    // Get all permutations
    val templates = for(inputPermutation <- newInputs.permutations.toStream) yield {
      val (exprs, result3) = gatherInputs(ctx2, inputPermutation.toList)
      ctx2 = ctx2.copy(result=result3)
      /* Add post, pre and in-between holes, and returns a single expr along with the new assignments. */
      val template: Stream[WithIds[Expr]] = exprs match {
        case Nil =>
          Stream(StringTemplateGenerator(Hole => Hole).instantiateWithVars)
        case exprList =>
          JoinProgramSet(exprList.map(DirectProgramSet(_)), (exprs: Seq[WithIds[Expr]]) =>
              StringTemplateGenerator.nested(Hole => {
                val res = ((StringConcat(Hole, exprs.head._1), exprs.head._2) /: exprs.tail) {
                  case ((finalExpr, finalIds), (expr, ids)) => (StringConcat(StringConcat(finalExpr, Hole), expr), finalIds ++ ids)
                }
                (StringConcat(res._1, Hole), res._2)
              }).instantiateWithVars
          ).programs
      }
      template
    }
    (templates.flatten, ctx2.result) // TODO: Flatten or interleave?
  }
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    //hctx.reporter.debug("StringRender:Output variables="+p.xs+", their types="+p.xs.map(_.getType))
    p.xs match {
      case List(IsTyped(v, StringType)) =>
        val description = "Creates a standard string conversion function"
        
        val defaultToStringFunctions = defaultMapTypeToString()
        
        val examplesFinder = new ExamplesFinder(hctx.context, hctx.program)
        val examples = examplesFinder.extractFromProblem(p)
        
        val ruleInstantiations = ListBuffer[RuleInstantiation]()
        ruleInstantiations += RuleInstantiation("String conversion") {
          val (expr, synthesisResult) = createFunDefsTemplates(StringSynthesisContext.empty, p.as.map(Variable))
          val funDefs = synthesisResult.adtToString
          
          /*val toDebug: String = (("\nInferred functions:" /: funDefs)( (t, s) =>
                t + "\n" + s._2._1.toString
              ))*/
          //hctx.reporter.debug("Inferred expression:\n" + expr + toDebug)
          
          findSolutions(examples, expr, funDefs.values.toSeq)
        }
        
        ruleInstantiations.toList
        
      case _ => Nil
    }
  }
}