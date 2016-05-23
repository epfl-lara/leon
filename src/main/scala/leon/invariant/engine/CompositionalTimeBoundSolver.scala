/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import transformations._
import invariant.structure.FunctionUtils._
import leon.invariant.structure.Formula
import leon.invariant.structure.Call
import leon.invariant.util._
import leon.invariant.factories.TemplateSolverFactory
import leon.invariant.util.Minimizer
import leon.solvers.Model
import Util._
import PredicateUtil._
import ProgramUtil._
import invariant.factories.TemplateInstantiator._

class CompositionalTimeBoundSolver(ctx: InferenceContext, prog: Program, rootFd: FunDef)
  extends FunctionTemplateSolver {

  val printIntermediatePrograms = false
  val debugDecreaseConstraints = false
  val debugComposition = false
  val reporter = ctx.reporter

  def inferTemplate(instProg: Program) = {
    (new UnfoldingTemplateSolver(ctx, instProg, findRoot(instProg)))()
  }

  def findRoot(prog: Program) = {
    functionByName(rootFd.id.name, prog).get
  }

  def apply() = {
    // Check if all the three templates have different template variable sets
    val (Some(tprTmpl), Some(recTmpl), Some(timeTmpl), othersTmpls) = extractSeparateTemplates(rootFd)
    val tmplIds = (Seq(tprTmpl, recTmpl, timeTmpl) ++ othersTmpls) flatMap getTemplateIds
    if (tmplIds.toSet.size < tmplIds.size)
      throw new IllegalStateException("Templates for tpr, rec, time as well as all other templates " +
        " taken together should not have the any common template variables for compositional analysis")

    val origProg = prog
    // add only rec templates for all functions
    val funToRecTmpl = userLevelFunctions(origProg).collect {
      case fd if fd.hasTemplate && fd == rootFd =>
        fd -> recTmpl
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }.toMap
    val recProg = assignTemplateAndCojoinPost(funToRecTmpl, origProg)

    // add only tpr template for all functions
    val funToNonRecTmpl = userLevelFunctions(origProg).collect {
      case fd if fd.hasTemplate && fd == rootFd =>
        fd -> tprTmpl
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }.toMap
    val tprProg = assignTemplateAndCojoinPost(funToNonRecTmpl, origProg)

    if (printIntermediatePrograms) {
      reporter.info("RecProg:\n" + recProg)
      reporter.info("TRPProg: \n" + tprProg)
    }
    val recInfRes = inferTemplate(recProg)
    val tprInfRes = inferTPRTemplate(tprProg)

    (recInfRes, tprInfRes) match {
      case (Some(InferResult(true, Some(recModel), _)),
        Some(InferResult(true, Some(tprModel), _))) =>
        // create a new program by omitting the templates of the root function
        val funToTmpl = userLevelFunctions(origProg).collect {
          case fd if fd.hasTemplate && fd != rootFd =>
            (fd -> fd.getTemplate)
        }.toMap
        val compProg = assignTemplateAndCojoinPost(funToTmpl, origProg)
        val compFunDef = findRoot(compProg)
        //val nctx = ctx.copy(program = compProg)

        // construct the instantiated tpr bound and check if it monotonically decreases
        val Operator(Seq(_, tprFun), _) = tprTmpl
        val tprFunInst = (new RealToInt()).mapExpr(
          replace(tprModel.map { case (k, v) => (k.toVariable -> v) }.toMap, tprFun))
        // TODO: this would fail on non-integers, handle these by approximating to the next bigger integer

        // Upper bound on time time <= recFun * tprFun + tprFun
        val (_, multFun) = MultFuncs.getMultFuncs(if (ctx.usereals) RealType else IntegerType)
        val Operator(Seq(_, recFun), _) = recTmpl
        val recFunInst = (new RealToInt()).mapExpr(
          replace(recModel.map { case (k, v) => (k.toVariable -> v) }.toMap, recFun))

        val timeUpperBound = ExpressionTransformer.normalizeMultiplication(
          Plus(FunctionInvocation(TypedFunDef(multFun, Seq()),
            Seq(recFunInst, tprFunInst)), tprFunInst), ctx.multOp)

        // map the old functions in the vc using the new functions
        val substMap = origProg.definedFunctions.collect {
          case fd => (fd -> functionByName(fd.id.name, compProg).get)
        }.toMap
        // res = body
        val body = mapFunctionsInExpr(substMap)(Equals(getResId(rootFd).get.toVariable, rootFd.body.get))
        val pre = rootFd.precondition.getOrElse(tru)
        val Operator(Seq(timeInstExpr, _), _) = timeTmpl
        val trans = mapFunctionsInExpr(substMap) _
        val assump = trans(createAnd(Seq(LessEquals(timeInstExpr, timeUpperBound), pre)))
        val conseq = trans(timeTmpl)

        if (printIntermediatePrograms) reporter.info("Comp prog: " + compProg)
        if (debugComposition) reporter.info("Compositional VC: " + createAnd(Seq(assump, body, Not(conseq))))

        val recTempSolver = new UnfoldingTemplateSolver(ctx, compProg, compFunDef) {
          val minFunc = {
            val mizer = new Minimizer(ctx, compProg)
            Some(mizer.minimizeBounds(mizer.computeCompositionLevel(timeTmpl)) _)
          }
          override lazy val templateSolver =
            TemplateSolverFactory.createTemplateSolver(ctx, compProg, constTracker, rootFd, minFunc)
          override def instantiateModel(model: Model, funcs: Seq[FunDef]) = {
            funcs.collect {
              case `compFunDef` => compFunDef -> timeTmpl
              case fd if fd.hasTemplate =>
                fd -> instantiateNormTemplates(model, fd.normalizedTemplate.get)
            }.toMap
          }
        }
        recTempSolver.solveParametricVC(assump, body, conseq) match {
          case Some(InferResult(true, Some(timeModel),timeInferredFuncs)) =>
            val inferredFuns = (recInfRes.get.inferredFuncs ++ tprInfRes.get.inferredFuncs ++ timeInferredFuncs).distinct
            Some(InferResult(true, Some(recModel ++ tprModel.toMap ++ timeModel.toMap),
              inferredFuns.map(ifd => functionByName(ifd.id.name, origProg).get).distinct))
          case res @ _ =>
            res
        }
      case _ =>
        reporter.info("Could not infer bounds on rec and(or) tpr. Cannot precced with composition.")
        None
    }
  }

  def extractSeparateTemplates(funDef: FunDef): (Option[Expr], Option[Expr], Option[Expr], Seq[Expr]) = {
    if (!funDef.hasTemplate) (None, None, None, Seq[Expr]())
    else {
      val template = ExpressionTransformer.pullAndOrs(And(funDef.getTemplate,
          funDef.getPostWoTemplate)) // note that some bounds can occur in post and not in tmpl
      def extractTmplConjuncts(tmpl: Expr): Seq[Expr] = {
        tmpl match {
          case And(seqExprs) =>
            seqExprs
          case _ =>
            throw new IllegalStateException("Compositional reasoning requires templates to be conjunctions!" + tmpl)
        }
      }
      val tmplConjuncts = extractTmplConjuncts(template)
      val tupleSelectToInst = InstUtil.getInstMap(funDef)
      var tprTmpl: Option[Expr] = None
      var timeTmpl: Option[Expr] = None
      var recTmpl: Option[Expr] = None
      var othersTmpls: Seq[Expr] = Seq[Expr]()
      tmplConjuncts.foreach {
        case conj@Operator(Seq(lhs, _), _) if (tupleSelectToInst.contains(lhs)) =>
          tupleSelectToInst(lhs) match {
            case n if n == TPR.name =>
              tprTmpl = Some(conj)
            case n if n == Time.name =>
              timeTmpl = Some(conj)
            case n if n == Rec.name =>
              recTmpl = Some(conj)
            case _ =>
              othersTmpls = othersTmpls :+ conj
          }
        case conj =>
          othersTmpls = othersTmpls :+ conj
      }
      (tprTmpl, recTmpl, timeTmpl, othersTmpls)
    }
  }

  def inferTPRTemplate(tprProg: Program) = {
    val tempSolver = new UnfoldingTemplateSolver(ctx, tprProg, findRoot(tprProg)) {
      override def constructVC(rootFd: FunDef): (Expr, Expr, Expr) = {
        val body = Equals(getResId(rootFd).get.toVariable, rootFd.body.get)
        val preExpr = rootFd.precondition.getOrElse(tru)
        val tprTmpl = rootFd.getTemplate
        val postWithTemplate = And(rootFd.getPostWoTemplate, tprTmpl)
        // generate constraints characterizing decrease of the tpr function with recursive calls
        val Operator(Seq(_, tprFun), op) = tprTmpl
        val bodyFormula = new Formula(rootFd, ExpressionTransformer.normalizeExpr(body, ctx.multOp), ctx)
        val constraints = bodyFormula.callsInFormula.collect {
          case call @ Call(_, FunctionInvocation(TypedFunDef(`rootFd`, _), _)) => //direct recursive call ?
            val cdata = bodyFormula.callData(call)
            Implies(cdata.guard, LessEquals(replace(formalToActual(call), tprFun), tprFun))
        }
        if (debugDecreaseConstraints)
          reporter.info("Decrease constraints: " + createAnd(constraints.toSeq))

        val fullPost = createAnd(postWithTemplate +: constraints.toSeq)
        (bodyFormula.toExpr, preExpr, fullPost)
      }
    }
    tempSolver()
  }
}