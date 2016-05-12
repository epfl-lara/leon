/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import evaluators.AbstractEvaluator
import purescala.Definitions._
import purescala.Common._
import purescala.Types._
import purescala.Constructors._
import purescala.Expressions._
import purescala.Extractors._
import purescala.TypeOps
import purescala.DefOps
import purescala.ExprOps
import purescala.SelfPrettyPrinter
import solvers.ModelBuilder
import solvers.string.StringSolver
import programsets.DirectProgramSet
import programsets.JoinProgramSet

/** A template generator for a given type tree. 
  * Extend this class using a concrete type tree,
  * Then use the apply method to get a hole which can be a placeholder for holes in the template.
  * Each call to the `.instantiate` method of the subsequent Template will provide different instances at each position of the hole.
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
  
  var enforceDefaultStringMethodsIfAvailable = true
  var enforceSelfStringMethodsIfAvailable = false
  
  val booleanTemplate = (a: Expr) => StringTemplateGenerator(Hole => IfExpr(a, Hole, Hole))
  
  import StringSolver.{StringFormToken, Problem => SProblem, Equation, Assignment}
  
  /** Augment the left-hand-side to have possible function calls, such as x + "const" + customToString(_) ...
   *  Function calls will be eliminated when converting to a valid problem.
   */
  sealed abstract class AugmentedStringFormToken
  case class RegularStringFormToken(e: StringFormToken) extends AugmentedStringFormToken
  case class OtherStringFormToken(e: Expr) extends AugmentedStringFormToken
  type AugmentedStringForm = List[AugmentedStringFormToken]
  
  /** Augments the right-hand-side to have possible function calls, such as "const" + customToString(_) ... 
   *  Function calls will be eliminated when converting to a valid problem.
   */
  sealed abstract class AugmentedStringChunkRHS
  case class RegularStringChunk(e: String) extends AugmentedStringChunkRHS
  case class OtherStringChunk(e: Expr) extends AugmentedStringChunkRHS
  type AugmentedStringLiteral = List[AugmentedStringChunkRHS]
  
  /** Converts an expression to a stringForm, suitable for StringSolver */
  def toStringForm(e: Expr, acc: List[AugmentedStringFormToken] = Nil)(implicit hctx: SearchContext): Option[AugmentedStringForm] = e match {
    case StringLiteral(s) => 
      Some(RegularStringFormToken(Left(s))::acc)
    case Variable(id) => Some(RegularStringFormToken(Right(id))::acc)
    case StringConcat(lhs, rhs) => 
      toStringForm(rhs, acc).flatMap(toStringForm(lhs, _))
    case e:Application => Some(OtherStringFormToken(e)::acc)
    case e:FunctionInvocation => Some(OtherStringFormToken(e)::acc)
    case _ => None
  }
  
  /** Returns the string associated to the expression if it is computable */
  def toStringLiteral(e: Expr): Option[AugmentedStringLiteral] = e match {
    case StringLiteral(s) => Some(List(RegularStringChunk(s)))
    case StringConcat(lhs, rhs) =>
      toStringLiteral(lhs).flatMap(k => toStringLiteral(rhs).map(l => (k.init, k.last, l) match {
        case (kinit, RegularStringChunk(s), RegularStringChunk(sp)::ltail) =>
          kinit ++ (RegularStringChunk(s + sp)::ltail)
        case _ => k ++ l
      }))
    case e: Application => Some(List(OtherStringChunk(e)))
    case e: FunctionInvocation => Some(List(OtherStringChunk(e)))
    case _ => None
  }
  
  /** Converts an equality AugmentedStringForm == AugmentedStringLiteral to a list of equations
   *  For that, splits both strings on function applications. If they yield the same value, we can split, else it fails. */
  def toEquations(lhs: AugmentedStringForm, rhs: AugmentedStringLiteral): Option[List[Equation]] = {
    def rec(lhs: AugmentedStringForm, rhs: AugmentedStringLiteral,
        accEqs: ListBuffer[Equation], accLeft: ListBuffer[StringFormToken], accRight: StringBuffer): Option[List[Equation]] = (lhs, rhs) match {
      case (Nil, Nil) =>
        (accLeft.toList, accRight.toString) match {
          case (Nil, "") => Some(accEqs.toList)
          case (lhs, rhs) => Some((accEqs += ((lhs, rhs))).toList)
        }
      case (OtherStringFormToken(e)::lhstail, OtherStringChunk(f)::rhstail) =>
        if(ExprOps.canBeHomomorphic(e, f).nonEmpty) {
          rec(lhstail, rhstail, accEqs += ((accLeft.toList, accRight.toString)), ListBuffer[StringFormToken](), new StringBuffer)
        } else None
      case (OtherStringFormToken(e)::lhstail, Nil) =>
        None
      case (Nil, OtherStringChunk(f)::rhstail) =>
        None
      case (lhs, RegularStringChunk(s)::rhstail) =>
        rec(lhs, rhstail, accEqs, accLeft, accRight append s)
      case (RegularStringFormToken(e)::lhstail, rhs) =>
        rec(lhstail, rhs, accEqs, accLeft += e, accRight)
    }
    rec(lhs, rhs, ListBuffer[Equation](), ListBuffer[StringFormToken](), new StringBuffer)
  }
  
  /** Returns a stream of assignments compatible with input/output examples for the given template */
  def findAssignments(p: Program, inputs: Seq[Identifier], examples: ExamplesBank, template: Expr)(implicit hctx: SearchContext): Stream[Map[Identifier, String]] = {

    val e = new AbstractEvaluator(hctx, p)
    
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
              hctx.reporter.info("Eval = None : ["+template+"] in ["+inputs.zip(in)+"]")
              hctx.reporter.info(evalResult)
              None
            case Some((sfExpr, abstractSfExpr)) =>
              //ctx.reporter.debug("Eval = ["+sfExpr+"] (from "+abstractSfExpr+")")
              val sf = toStringForm(sfExpr)
              val rhs = toStringLiteral(rhExpr.head)
              (sf, rhs) match {
                case (Some(sfget), Some(rhsget)) =>
                  toEquations(sfget, rhsget) match {
                    case Some(equations) =>
                      gatherEquations(q, acc ++= equations)
                    case None =>
                      hctx.reporter.info("Could not extract equations from ["+sfget+"] == ["+rhsget+"]\n coming from ... == " + rhExpr)
                    None
                  }
                case _ =>
                  hctx.reporter.info("sf empty or rhs empty ["+sfExpr+"] => ["+sf+"] in ["+rhs+"]")
                  None
              }
          }
        } else {
          hctx.reporter.info("RHS.length != 1 : ["+rhExpr+"]")
          None 
        }
    }
    gatherEquations((examples.valids ++ examples.invalids).collect{ case io:InOutExample => io }.toList) match {
      case Some(problem) => StringSolver.solve(problem)
      case None => Stream.empty
    }
  }
  
  /** With a given (template, fundefs, consts) will find consts so that (expr, funs) passes all the examples */
  def findSolutions(examples: ExamplesBank, template: Stream[WithIds[Expr]], funDefs: Seq[(FunDef, Stream[WithIds[Expr]])])(implicit hctx: SearchContext, p: Problem): RuleApplication = {
    // Fun is a stream of many function applications.
    val funs= JoinProgramSet.direct(funDefs.map(fbody => fbody._2.map((fbody._1, _))).map(d => DirectProgramSet(d)))
    
    val wholeTemplates = JoinProgramSet.direct(funs, DirectProgramSet(template))
    
    def computeSolutions(funDefsBodies: Seq[(FunDef, WithIds[Expr])], template: WithIds[Expr]): Stream[Assignment] = {
      val funDefs = for((funDef, body) <- funDefsBodies) yield  { funDef.body = Some(body._1); funDef }
      val newProgram = DefOps.addFunDefs(hctx.program, funDefs, hctx.functionContext)
      findAssignments(newProgram, p.as.filter{ x => !x.getType.isInstanceOf[FunctionType] }, examples, template._1)
    }
    
    val tagged_solutions =
      for{(funDefs, template) <- wholeTemplates.programs} yield computeSolutions(funDefs, template).map((funDefs, template, _))
    
    solutionStreamToRuleApplication(p, leon.utils.StreamUtils.interleave(tagged_solutions))(hctx.program)
  }
  
  /** Find ambiguities not containing _edit_me_ to ask to the user */
  def askQuestion(input: List[Identifier], r: RuleClosed)(implicit c: LeonContext, p: Program): List[disambiguation.Question[StringLiteral]] = {
    //if !s.contains(EDIT_ME)
    val qb = new disambiguation.QuestionBuilder(input, r.solutions, (seq: Seq[Expr], expr: Expr) => expr match {
      case s @ StringLiteral(slv) if !slv.contains(EDIT_ME) => Some(s)
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
            
            Solution(BooleanLiteral(true), finalDefs, finalTerm)
          })
    }
  }
  
  /** Crystallizes a solution so that it will not me modified if the body of fds is modified. */
  def makeFunctionsUnique(term: Expr, fds: Set[FunDef])(implicit program: Program): (Expr, Set[FunDef]) = {
    var transformMap = Map[FunDef, FunDef]()
    def mapExpr(body: Expr): Expr = {
      ExprOps.preMap((e: Expr) => e match {
        case FunctionInvocation(TypedFunDef(fd, _), args) if fds(fd) => Some(functionInvocation(getMapping(fd), args))
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
  type StringConverters = Map[TypeTree, List[Expr => Expr]]
  
  /** Companion object to create a StringSynthesisContext */
  object StringSynthesisContext {
    def empty(
        abstractStringConverters: StringConverters,
        originalInputs: Set[Expr],
        provided_functions: Seq[Identifier])(implicit hctx: SearchContext) =
      new StringSynthesisContext(None, new StringSynthesisResult(Map(), Set()),
        abstractStringConverters,
        originalInputs,
        provided_functions)
  }
  
  /** Context for the current synthesis process */
  class StringSynthesisContext(
      val currentCaseClassParent: Option[TypeTree],
      val result: StringSynthesisResult,
      val abstractStringConverters: StringConverters,
      val originalInputs: Set[Expr],
      val provided_functions: Seq[Identifier]
  )(implicit hctx: SearchContext) {
    def add(d: DependentType, f: FunDef, s: Stream[WithIds[Expr]]): StringSynthesisContext = {
      new StringSynthesisContext(currentCaseClassParent, result.add(d, f, s),
          abstractStringConverters,
          originalInputs,
          provided_functions)
    }
    def copy(currentCaseClassParent: Option[TypeTree]=currentCaseClassParent, result: StringSynthesisResult = result): StringSynthesisContext = 
      new StringSynthesisContext(currentCaseClassParent, result,
          abstractStringConverters,
          originalInputs,
          provided_functions)
    def freshFunName(s: String) = result.freshFunName(s)
  }
  
  /** Creates an empty function definition for the dependent type */
  def createEmptyFunDef(ctx: StringSynthesisContext, tpe: DependentType)(implicit hctx: SearchContext): FunDef = {
    def defaultFunName(t: TypeTree) = t match {
      case AbstractClassType(c, d) => c.id.asString(hctx)
      case CaseClassType(c, d) => c.id.asString(hctx)
      case t => t.asString(hctx)
    }
    
    val funName2 = tpe.caseClassParent match {
      case None => defaultFunName(tpe.typeToConvert) + "_" + tpe.inputName + "_s" 
      case Some(t) => defaultFunName(tpe.typeToConvert) + "In"+defaultFunName(t) + "_" + tpe.inputName + "_s" 
    }
    val funName3 = funName2.replaceAll("[^a-zA-Z0-9_]","")
    val funName = funName3(0).toLower + funName3.substring(1) 
    val funId = FreshIdentifier(ctx.freshFunName(funName), alwaysShowUniqueID = true)
    val argId= FreshIdentifier(tpe.typeToConvert.asString(hctx).toLowerCase()(0).toString, tpe.typeToConvert)
    val tparams = hctx.functionContext.tparams
    new FunDef(funId, tparams, ValDef(argId) :: ctx.provided_functions.map(ValDef).toList, StringType) // Empty function.
  }
  
  /** Pre-updates of the function definition */
  def preUpdateFunDefBody(tpe: DependentType, fd: FunDef, ctx: StringSynthesisContext): StringSynthesisContext = {
    ctx.result.adtToString.get(tpe) match {
      case None => ctx.add(tpe, fd, Stream.Empty)
      case Some(_) => ctx
    }
  }

  /** Assembles multiple MatchCase to a singleMatchExpr using the function definition fd */
  private val mergeMatchCases = (fd: FunDef) => (cases: Seq[WithIds[MatchCase]]) => (MatchExpr(Variable(fd.params(0).id), cases.map(_._1)), cases.flatMap(_._2).toList)
  
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
      case CaseClassType(ccd: CaseClassDef, tparams2) =>
        val typeMap = ccd.typeArgs.zip(tparams2).toMap
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
        case (acc, cct @ CaseClassType(ccd, tparams2)) =>
          val typeMap = ccd.typeArgs.zip(tparams2).toMap
          val fields = ccd.fields.map(vd => TypeOps.instantiateType(vd.id, typeMap) )
          val pattern = CaseClassPattern(None, ccd.typed(tparams2), fields.map(k => WildcardPattern(Some(k))))
          val rhs = StringLiteral(ccd.id.asString)
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
        val dependentType = DependentType(ctx.currentCaseClassParent, input.asString(hctx.program)(hctx), input.getType)
        ctx.result.adtToString.get(dependentType) match {
        case Some(fd) =>
          gatherInputs(ctx, q, result += Stream((functionInvocation(fd._1, input::ctx.provided_functions.toList.map(Variable)), Nil)))
        case None => // No function can render the current type.
          // We should not rely on calling the original function on the first line of the body of the function itself.
          val exprs1s = (new SelfPrettyPrinter)
            .allowFunction(hctx.functionContext)
            .excludeFunction(hctx.functionContext)
            .withPossibleParameters.prettyPrintersForType(input.getType)(hctx, hctx.program)
            .map{ case (l, identifiers) => (application(l, Seq(input)), identifiers) } // Use already pre-defined pretty printers.
          val exprs1 = exprs1s.toList.sortBy{ case (Lambda(_, FunctionInvocation(tfd, _)), _) if tfd.fd == hctx.functionContext => 0 case _ => 1}
          val exprs2 = ctx.abstractStringConverters.getOrElse(input.getType, Nil).map(f => (f(input), List[Identifier]()))
          val defaultConverters: Stream[WithIds[Expr]] = exprs1.toStream #::: exprs2.toStream
          val recursiveConverters: Stream[WithIds[Expr]] =
            (new SelfPrettyPrinter)
            .prettyPrinterFromCandidate(hctx.functionContext, input.getType)(hctx, hctx.program)
            .map(l => (application(l, Seq(input)), List[Identifier]()))
            
          def mergeResults(templateConverters: =>Stream[WithIds[Expr]]): Stream[WithIds[Expr]] = {
            if(defaultConverters.isEmpty) templateConverters
            else if(enforceDefaultStringMethodsIfAvailable) {
              if(enforceSelfStringMethodsIfAvailable)
                recursiveConverters #::: defaultConverters 
              else {
                defaultConverters #::: recursiveConverters
              }
            }
            else  recursiveConverters #::: defaultConverters #::: templateConverters
          }
          
          input.getType match {
            case StringType =>
              gatherInputs(ctx, q, result +=
                mergeResults(Stream((input, Nil),
                        (functionInvocation(
                            hctx.program.library.escape.get, List(input)): Expr, Nil))))
            case BooleanType =>
              val (bTemplate, vs) = booleanTemplate(input).instantiateWithVars
              gatherInputs(ctx, q, result += mergeResults(Stream((BooleanToString(input), Nil), (bTemplate, vs))))
            case WithStringconverter(converter) => // Base case
              gatherInputs(ctx, q, result += mergeResults(Stream((converter(input), Nil))))
            case t: ClassType =>
              if(enforceDefaultStringMethodsIfAvailable && defaultConverters.nonEmpty) {
                gatherInputs(ctx, q, result += defaultConverters)
              } else {
                // Create the empty function body and updates the assignments parts.
                val fd = createEmptyFunDef(ctx, dependentType)
                val ctx2 = preUpdateFunDefBody(dependentType, fd, ctx) // Inserts the FunDef in the assignments so that it can already be used.
                t.root match {
                  case act @ AbstractClassType(acd, tps) =>
                    // Create a complete FunDef body with pattern matching
                    
                    val allKnownDescendantsAreCCAndHaveZeroArgs = act.knownCCDescendants.forall {
                      case CaseClassType(ccd, tparams2) => ccd.fields.isEmpty
                      case _ => false
                    }
                    
                    //TODO: Test other templates not only with Wilcard patterns, but more cases options for non-recursive classes (e.g. Option, Boolean, Finite parameterless case classes.)
                    val (ctx3, cases) = ((ctx2, ListBuffer[Stream[WithIds[MatchCase]]]()) /: act.knownCCDescendants) {
                      case ((ctx22, acc), cct @ CaseClassType(ccd, tparams2)) =>
                        val (newCases, result) = extractCaseVariants(cct, ctx22)
                        val ctx23 = ctx22.copy(result = result)
                        (ctx23, acc += newCases)
                      case ((adtToString, acc), e) => hctx.reporter.fatalError("Could not handle this class definition for string rendering " + e)
                    }
                    
                    val allMatchExprsEnd = JoinProgramSet(cases.map(DirectProgramSet(_)), mergeMatchCases(fd)).programs // General pattern match expressions
                    val allMatchExprs = if(allKnownDescendantsAreCCAndHaveZeroArgs) {
                      Stream(constantPatternMatching(fd, act)) ++ allMatchExprsEnd
                    } else allMatchExprsEnd
                    gatherInputs(ctx3.add(dependentType, fd, allMatchExprs), q,
                        result += Stream((functionInvocation(fd, input::ctx.provided_functions.toList.map(Variable)), Nil)))
                  case cct @ CaseClassType(ccd, tparams2) =>
                    val (newCases, result3) = extractCaseVariants(cct, ctx2)
                    val allMatchExprs = newCases.map(acase => mergeMatchCases(fd)(Seq(acase)))
                    gatherInputs(ctx2.copy(result = result3).add(dependentType, fd, allMatchExprs), q,
                        result += Stream((functionInvocation(fd, input::ctx.provided_functions.toList.map(Variable)), Nil)))
                }
              }
            case TypeParameter(t) =>
              if(defaultConverters.isEmpty) {
                hctx.reporter.fatalError("Could not handle type parameter for string rendering " + t)
              } else {
                gatherInputs(ctx, q, result += mergeResults(Stream.empty))
              }
              
            case t: SetType =>
              gatherInputs(ctx, q, result += defaultConverters)
            case t: BagType =>
              gatherInputs(ctx, q, result += defaultConverters)
            case t: MapType =>
              gatherInputs(ctx, q, result += defaultConverters)
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
    (templates.flatten, ctx2.result)
  }
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    //hctx.reporter.debug("StringRender:Output variables="+p.xs+", their types="+p.xs.map(_.getType))
    p.xs match {
      case List(IsTyped(v, StringType)) =>
        val examplesFinder = new ExamplesFinder(hctx, hctx.program)
          .setKeepAbstractExamples(true)
          .setEvaluationFailOnChoose(true)

        val examples = examplesFinder.extractFromProblem(p)
        
        val abstractStringConverters: StringConverters = p.as.flatMap { case x =>
          x.getType match {
            case FunctionType(Seq(aType), StringType) =>
              List((aType, (arg: Expr) => application(Variable(x), Seq(arg))))
            case _ => Nil
          }
        }.groupBy(_._1).mapValues(_.map(_._2))
       
        val (inputVariables, functionVariables) = p.as.partition ( x => x.getType match {
          case f: FunctionType => false
          case _ => true
        })
        
        val ruleInstantiations = ListBuffer[RuleInstantiation]()
        val originalInputs = inputVariables.map(Variable)
        ruleInstantiations += RuleInstantiation("String conversion") {
          val (expr, synthesisResult) = createFunDefsTemplates(
            StringSynthesisContext.empty(
              abstractStringConverters,
              originalInputs.toSet,
              functionVariables
            ), originalInputs
          )
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
