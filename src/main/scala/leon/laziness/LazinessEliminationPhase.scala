package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import leon.verification.AnalysisPhase
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.TransformationPhase
import LazinessUtil._
import leon.invariant.datastructure.DisjointSets

object LazinessEliminationPhase extends TransformationPhase {
  val debugLifting = false
  val dumpProgramWithClosures = false
  val dumpTypeCorrectProg = false
  val dumpProgWithPreAsserts = false
  val dumpInstrumentedProgram = false
  val debugSolvers = false

  val skipVerification = false
  val prettyPrint = true

  val name = "Laziness Elimination Phase"
  val description = "Coverts a program that uses lazy construct" +
    " to a program that does not use lazy constructs"

  /**
   * TODO: enforce that the specs do not create lazy closures
   * TODO: we are forced to make an assumption that lazy ops takes as type parameters only those
   * type parameters of their return type and not more. (enforce this)
   * TODO: Check that lazy types are not nested
   */
  def apply(ctx: LeonContext, prog: Program): Program = {

    val nprog = liftLazyExpressions(prog)
    val progWithClosures = (new LazyClosureConverter(nprog, new LazyClosureFactory(nprog))).apply
    if (dumpProgramWithClosures)
      println("After closure conversion: \n" + ScalaPrinter.apply(progWithClosures))

    //Rectify type parameters and local types
    val typeCorrectProg = (new TypeRectifier(progWithClosures, tp => tp.id.name.endsWith("@"))).apply
    if (dumpTypeCorrectProg)
      println("After rectifying types: \n" + ScalaPrinter.apply(typeCorrectProg))

    val progWithPre = (new ClosurePreAsserter(typeCorrectProg)).apply
    if (dumpProgWithPreAsserts)
      println("After asserting closure preconditions: \n" + ScalaPrinter.apply(progWithPre))

    // instrument the program for resources
    val instProg = (new LazyInstrumenter(progWithPre)).apply
    if(dumpInstrumentedProgram)
      println("After instrumentation: \n" + ScalaPrinter.apply(instProg))

    // check specifications (to be moved to a different phase)
    if (!skipVerification)
      checkSpecifications(instProg)
    if (prettyPrint)
      prettyPrintProgramToFile(instProg, ctx)
    instProg
  }

  /**
   * convert the argument of every lazy constructors to a procedure
   */
  def liftLazyExpressions(prog: Program): Program = {
    var newfuns = Map[ExprStructure, (FunDef, ModuleDef)]()
    var anchorFun: Option[FunDef] = None // Fix this way of finding anchor functions
    val fdmap = prog.modules.flatMap { md =>
      md.definedFunctions.map {
        case fd if fd.hasBody && !fd.isLibrary =>
          //println("FunDef: "+fd)
          val nfd = preMapOnFunDef {
            case finv @ FunctionInvocation(lazytfd, Seq(arg)) if isLazyInvocation(finv)(prog) && !arg.isInstanceOf[FunctionInvocation] =>
              val freevars = variablesOf(arg).toList
              val tparams = freevars.map(_.getType) flatMap getTypeParameters
              val argstruc = new ExprStructure(arg)
              val argfun =
                if (newfuns.contains(argstruc)) {
                  newfuns(argstruc)._1
                } else {
                  //construct type parameters for the function
                  val nfun = new FunDef(FreshIdentifier("lazyarg", arg.getType, true),
                    tparams map TypeParameterDef.apply, arg.getType, freevars.map(ValDef(_)))
                  nfun.body = Some(arg)
                  newfuns += (argstruc -> (nfun, md))
                  nfun
                }
              Some(FunctionInvocation(lazytfd, Seq(FunctionInvocation(TypedFunDef(argfun, tparams),
                freevars.map(_.toVariable)))))
            case _ => None
          }(fd)
          (fd -> Some(nfd))
        case fd => fd -> Some(fd.duplicate)
      }
    }.toMap
    // map  the new functions to themselves
    val newfdMap = newfuns.values.map { case (nfd, _) => nfd -> None }.toMap
    val (repProg, _) = replaceFunDefs(prog)(fdmap ++ newfdMap)
    val nprog =
      if (!newfuns.isEmpty) {
        val modToNewDefs = newfuns.values.groupBy(_._2).map { case (k, v) => (k, v.map(_._1)) }.toMap
        appendDefsToModules(repProg, modToNewDefs)
      } else
        throw new IllegalStateException("Cannot find any lazy computation")
    if (debugLifting)
      println("After lifiting arguments of lazy constructors: \n" + ScalaPrinter.apply(nprog))
    nprog
  }

  import leon.solvers._
  import leon.solvers.z3._

  def checkSpecifications(prog: Program) {
    // convert 'axiom annotation to library
    prog.definedFunctions.foreach { fd =>
      if (fd.annotations.contains("axiom"))
        fd.addFlag(Annotation("library", Seq()))
    }
    val functions = Seq() // Seq("--functions=rotate-time")
    val solverOptions = if(debugSolvers) Seq("--debug=solver") else Seq()
    val ctx = Main.processOptions(Seq("--solvers=smt-cvc4") ++ solverOptions ++ functions)
    val report = AnalysisPhase.run(ctx)(prog)
    println(report.summaryString)
    /*val timeout = 10
    val rep = ctx.reporter
     * val fun = prog.definedFunctions.find(_.id.name == "firstUnevaluated").get
    // create a verification context.
    val solver = new FairZ3Solver(ctx, prog) with TimeoutSolver
    val solverF = new TimeoutSolverFactory(SolverFactory(() => solver), timeout * 1000)
    val vctx = VerificationContext(ctx, prog, solverF, rep)
    val vc = (new DefaultTactic(vctx)).generatePostconditions(fun)(0)
    val s = solverF.getNewSolver()
    try {
      rep.info(s" - Now considering '${vc.kind}' VC for ${vc.fd.id} @${vc.getPos}...")
      val tStart = System.currentTimeMillis
      s.assertVC(vc)
      val satResult = s.check
      val dt = System.currentTimeMillis - tStart
      val res = satResult match {
        case None =>
          rep.info("Cannot prove or disprove specifications")
        case Some(false) =>
          rep.info("Valid")
        case Some(true) =>
          println("Invalid - counter-example: " + s.getModel)
      }
    } finally {
      s.free()
    }*/
  }

  /**
   * NOT USED CURRENTLY
   * Lift the specifications on functions to the invariants corresponding
   * case classes.
   * Ideally we should class invariants here, but it is not currently supported
   * so we create a functions that can be assume in the pre and post of functions.
   * TODO: can this be optimized
   */
  /*  def liftSpecsToClosures(opToAdt: Map[FunDef, CaseClassDef]) = {
    val invariants = opToAdt.collect {
      case (fd, ccd) if fd.hasPrecondition =>
        val transFun = (args: Seq[Identifier]) => {
          val argmap: Map[Expr, Expr] = (fd.params.map(_.id.toVariable) zip args.map(_.toVariable)).toMap
          replace(argmap, fd.precondition.get)
        }
        (ccd -> transFun)
    }.toMap
    val absTypes = opToAdt.values.collect {
      case cd if cd.parent.isDefined => cd.parent.get.classDef
    }
    val invFuns = absTypes.collect {
      case abs if abs.knownCCDescendents.exists(invariants.contains) =>
        val absType = AbstractClassType(abs, abs.tparams.map(_.tp))
        val param = ValDef(FreshIdentifier("$this", absType))
        val tparams = abs.tparams
        val invfun = new FunDef(FreshIdentifier(abs.id.name + "$Inv", Untyped),
            tparams, BooleanType, Seq(param))
        (abs -> invfun)
    }.toMap
    // assign bodies for the 'invfuns'
    invFuns.foreach {
      case (abs, fd) =>
        val bodyCases = abs.knownCCDescendents.collect {
          case ccd if invariants.contains(ccd) =>
            val ctype = CaseClassType(ccd, fd.tparams.map(_.tp))
            val cvar = FreshIdentifier("t", ctype)
            val fldids = ctype.fields.map {
              case ValDef(fid, Some(fldtpe)) =>
                FreshIdentifier(fid.name, fldtpe)
            }
            val pattern = CaseClassPattern(Some(cvar), ctype,
              fldids.map(fid => WildcardPattern(Some(fid))))
            val rhsInv = invariants(ccd)(fldids)
            // assert the validity of substructures
            val rhsValids = fldids.flatMap {
              case fid if fid.getType.isInstanceOf[ClassType] =>
                val t = fid.getType.asInstanceOf[ClassType]
                val rootDef = t match {
                  case absT: AbstractClassType => absT.classDef
                  case _ if t.parent.isDefined =>
                    t.parent.get.classDef
                }
                if (invFuns.contains(rootDef)) {
                  List(FunctionInvocation(TypedFunDef(invFuns(rootDef), t.tps),
                    Seq(fid.toVariable)))
                } else
                  List()
              case _ => List()
            }
            val rhs = Util.createAnd(rhsInv +: rhsValids)
            MatchCase(pattern, None, rhs)
        }
        // create a default case
        val defCase = MatchCase(WildcardPattern(None), None, Util.tru)
        val matchExpr = MatchExpr(fd.params.head.id.toVariable, bodyCases :+ defCase)
        fd.body = Some(matchExpr)
    }
    invFuns
  }*/
}
