package leon
package invariant.engine

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import invariant.templateSolvers._
import invariant.util.Util._
import transformations._
import invariant.structure.FunctionUtils._
import transformations.InstUtil._
import leon.invariant.structure.Formula
import leon.invariant.structure.Call
import leon.invariant.util.RealToInt
import leon.invariant.util.OrderedMultiMap
import leon.invariant.util.ExpressionTransformer
import leon.invariant.factories.TemplateSolverFactory
import leon.invariant.util.Minimizer
import leon.solvers.Model

class CompositionalTimeBoundSolver(ctx: InferenceContext, rootFd: FunDef)
  extends FunctionTemplateSolver {

  val printIntermediatePrograms = false
  val debugDecreaseConstraints = false
  val debugComposition = false
  val reporter = ctx.reporter

  def inferTemplate(instProg: Program) = {
    (new UnfoldingTemplateSolver(ctx.copy(program = instProg), findRoot(instProg)))()
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

    val origProg = ctx.program
    // add only rec templates for all functions
    val funToRecTmpl = origProg.definedFunctions.collect {
      case fd if fd.hasTemplate && fd == rootFd =>
        fd -> recTmpl
      case fd if fd.hasTemplate =>
        fd -> fd.getTemplate
    }.toMap
    val recProg = assignTemplateAndCojoinPost(funToRecTmpl, origProg)

    // add only tpr template for all functions
    val funToNonRecTmpl = origProg.definedFunctions.collect {
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
        val funToTmpl = origProg.definedFunctions.collect {
          case fd if fd.hasTemplate && fd != rootFd =>
            (fd -> fd.getTemplate)
        }.toMap
        val compProg = assignTemplateAndCojoinPost(funToTmpl, origProg)
        val compFunDef = findRoot(compProg)
        val nctx = ctx.copy(program = compProg)

        // construct the instantiated tpr bound and check if it monotonically decreases
        val Operator(Seq(_, tprFun), _) = tprTmpl
        val tprFunInst = (new RealToInt()).mapRealToInt(
          replace(tprModel.map { case (k, v) => (k.toVariable -> v) }.toMap, tprFun))
        // TODO: this would fail on non-integers, handle these by approximating to the next bigger integer

        // Upper bound on time time <= recFun * tprFun + tprFun
        val (_, multFun) = MultFuncs.getMultFuncs(if (ctx.usereals) RealType else IntegerType)
        val Operator(Seq(_, recFun), _) = recTmpl
        val recFunInst = (new RealToInt()).mapRealToInt(
          replace(recModel.map { case (k, v) => (k.toVariable -> v) }.toMap, recFun))

        val timeUpperBound = ExpressionTransformer.normalizeMultiplication(
          Plus(FunctionInvocation(TypedFunDef(multFun, Seq()),
            Seq(recFunInst, tprFunInst)), tprFunInst), ctx.multOp)
        // res = body
        val plainBody = Equals(getResId(rootFd).get.toVariable, matchToIfThenElse(rootFd.body.get))
        val bodyExpr = if (rootFd.hasPrecondition) {
          And(matchToIfThenElse(rootFd.precondition.get), plainBody)
        } else plainBody

        val Operator(Seq(timeInstExpr, _), _) = timeTmpl
        val compositionAnt = And(Seq(LessEquals(timeInstExpr, timeUpperBound), bodyExpr))
        val prototypeVC = And(compositionAnt, Not(timeTmpl))

        // map the old functions in the vc using the new functions
        val substMap = origProg.definedFunctions.collect {
          case fd =>
            (fd -> functionByName(fd.id.name, compProg).get)
        }.toMap
        val vcExpr = mapFunctionsInExpr(substMap)(prototypeVC)

        if (printIntermediatePrograms) reporter.info("Comp prog: " + compProg)
        if (debugComposition) reporter.info("Compositional VC: " + vcExpr)

        val recTempSolver = new UnfoldingTemplateSolver(nctx, compFunDef) {
          val minFunc = {
            val mizer = new Minimizer(ctx)
            Some(mizer.minimizeBounds(mizer.computeCompositionLevel(timeTmpl)) _)
          }
          override lazy val templateSolver =
            TemplateSolverFactory.createTemplateSolver(ctx, constTracker, rootFd, minFunc)
          override def instantiateModel(model: Model, funcs: Seq[FunDef]) = {
            funcs.collect {
              case `compFunDef` =>
                compFunDef -> timeTmpl
              case fd if fd.hasTemplate =>
                fd -> fd.getTemplate
            }.toMap
          }
        }
        recTempSolver.solveParametricVC(vcExpr) match {
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

  def combineMapsUsingConjunction(maps: List[Map[FunDef, Expr]]) = {
    val combMap = new OrderedMultiMap[FunDef, Expr]
    maps.foreach {
      _.foreach {
        case (k, v) =>
          val origFun = functionByName(k.id.name, ctx.program).get
          combMap.addBinding(origFun, v)
      }
    }
    combMap.foldLeft(Map[FunDef, Expr]()) {
      case (acc, (k, vs)) if vs.size == 1 => acc + (k -> vs(0))
      case (acc, (k, vs)) => acc + (k -> And(vs.toSeq))
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
      tmplConjuncts.foreach(conj => {
        conj match {
          case Operator(Seq(lhs, _), _) if (tupleSelectToInst.contains(lhs)) =>
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
          case _ =>
            othersTmpls = othersTmpls :+ conj
        }
      })
      (tprTmpl, recTmpl, timeTmpl, othersTmpls)
    }
  }

  def inferTPRTemplate(tprProg: Program) = {
    val tempSolver = new UnfoldingTemplateSolver(ctx.copy(program = tprProg), findRoot(tprProg)) {
      override def constructVC(rootFd: FunDef): (Expr, Expr) = {
        val body = Equals(getResId(rootFd).get.toVariable, matchToIfThenElse(rootFd.body.get))
        val preExpr =
          if (rootFd.hasPrecondition)
            matchToIfThenElse(rootFd.precondition.get)
          else tru
        val tprTmpl = rootFd.getTemplate
        val postWithTemplate = matchToIfThenElse(And(rootFd.getPostWoTemplate, tprTmpl))
        // generate constraints characterizing decrease of the tpr function with recursive calls
        val Operator(Seq(_, tprFun), op) = tprTmpl
        val bodyFormula = new Formula(rootFd, ExpressionTransformer.normalizeExpr(body, ctx.multOp), ctx)
        val constraints = bodyFormula.disjunctsInFormula.flatMap {
          case (guard, ctrs) =>
            ctrs.collect {
              case call @ Call(_, FunctionInvocation(TypedFunDef(`rootFd`, _), _)) => //direct recursive call ?
                Implies(guard, LessEquals(replace(formalToActual(call), tprFun), tprFun))
            }
        }
        if (debugDecreaseConstraints)
          reporter.info("Decrease constraints: " + createAnd(constraints.toSeq))

        val fullPost = createAnd(postWithTemplate +: constraints.toSeq)
        (And(preExpr, bodyFormula.toExpr), fullPost)
      }
    }
    tempSolver()
  }
}