/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Types._
import theorem._
import evaluators.ProofEvaluator
import evaluators.EvaluationResults._
import utils.DebugSection
import utils.DebugSectionProof

/** Tactic used for functions with explicit proof functions. */
class ManualTactic(vctx: VerificationContext) extends DefaultTactic(vctx) {
  import vctx.reporter

  private implicit val debugSection: DebugSection = DebugSectionProof
  private val library = Library(vctx.program)

  override val description = "Manual proof verification condition generation approach"

  override def generatePostconditions(fd: FunDef): Seq[VC] = {

    // Handling the case when the function has no post-condition.
    if (!fd.hasPostcondition) {
      reporter.warning("Function " + fd.qualifiedName(vctx.program) + " has no postcondition.")
      return Seq()
    }

    // Handling the case when the function has no body.
    if (!fd.hasBody) {
      reporter.fatalError("Function " + fd.qualifiedName(vctx.program) + " has an empty body.")
    }

    // Gets the proof function.
    val proofFd = getProofFd(fd)

    // Verification of the signature of the proof function.
    checkSignature(fd, proofFd)

    // Execute the proofs and generates verification conditions.
    executeProof(fd, proofFd)
  }

  /** Looks up the proof function. */
  private def getProofFd(fd: FunDef): FunDef = {

    // Getting the name of the proof from the annotation.
    val optProofName = for {
      optArgs <- fd.extAnnotations.get("manual")
      optFirstArg <- optArgs.headOption
      firstArg <- optFirstArg
      if firstArg.isInstanceOf[String]
    } yield firstArg.asInstanceOf[String]

    // Handling the case when the proof name is not specified.
    if (optProofName.isEmpty) {
      val errorMsg = "Proof function not specified in the " + 
        "@manual annotation of " + fd.qualifiedName(vctx.program) + "."
      reporter.fatalError(errorMsg)
    }

    val proofName = optProofName.get
    val optProofFd = vctx.program.lookupFunDef(proofName)

    // Handling the case when the proof function can not be found.
    if (optProofFd.isEmpty) {
      val errorMsg = "Proof function not found for " + 
        fd.qualifiedName(vctx.program) + "."
      reporter.fatalError(errorMsg)
    }

    val proofFd = optProofFd.get

    // Handling the case when the proof function does not have the @proof annotation.
    if (!proofFd.annotations.contains("proof")) {
      val errorMsg = "Proof function of " + 
        fd.qualifiedName(vctx.program) + ", " + 
        proofFd.qualifiedName(vctx.program) +
        ", does not have the @proof annotation."
      reporter.fatalError(errorMsg)
    }

    proofFd
  }

  /** Checks that the proof function has the correct signature.
    *
    * For a function of n arguments, the proof function must
    * have n consecutive arguments of type Identifier followed by
    * an argument of type Theorem (the precondition), and finally an
    * argument of type Term (the postconsition to be proven).
    * The proof function must return a Theorem.
    */
  private def checkSignature(fd: FunDef, proofFd: FunDef): Unit = {
    
    val theoremType = CaseClassType(library.Theorem.get, Seq())
    val identifierType = CaseClassType(library.Identifier.get, Seq())
    val termType = AbstractClassType(library.Term.get, Seq())

    val fdParams = fd.params
    val proofFdParams = proofFd.params
    val n = fdParams.size

    // The size of the arguments should be n + 2.
    if (proofFdParams.size != n + 2) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) + 
        " has wrong number of parameters."
      reporter.fatalError(errorMsg)
    }

    // The first n parameters should all be of type Identifier.
    for (i <- 0 until n) {
      if (proofFdParams(i).getType != identifierType) {
        val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
          " should take a leon.theorem.Identifier as its argument at position " + 
          (i + 1) + "."
        reporter.fatalError(errorMsg)
      }
    }

    // The next parameters should be the precondition, of type Theorem.
    if (proofFdParams(n).getType != theoremType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a precondition leon.theorem.Theorem as second-last argument."
      reporter.fatalError(errorMsg)
    }

    // The last parameter should be the post condition, of type Term.
    if (proofFdParams(n + 1).getType != termType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a postcondition leon.theorem.Term as last argument."
      reporter.fatalError(errorMsg)
    }

    // The return type should be a Theorem.
    if (proofFd.returnType != theoremType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should return a value of type leon.theorem.Theorem."
      reporter.fatalError(errorMsg)
    }
  }

  /** Evaluates the proof function and generates VCs. */
  def executeProof(fd: FunDef, proofFd: FunDef): Seq[VC] = {

    val encoder = new ExprEncoder(vctx)
    val evaluator = new ProofEvaluator(vctx, vctx.program)

    reporter.debug("Starting execution of the proof function " + proofFd.qualifiedName(vctx.program) + 
      " for function " + fd.qualifiedName(vctx.program))

    // Creating user-world identifiers for each parameter of the function.
    val mapping = for (vd <- fd.params) yield (vd.id -> encoder.identifier(vd.id.uniqueName))

    val env: Map[Identifier, Expr] = mapping.toMap

    // Encoding the postcondition and precondition.
    val postExpr = encoder.encodeExpr(application(fd.postcondition.get, Seq(fd.body.get)), env)
    val preExpr = encoder.caseClass(library.Theorem, encoder.encodeExpr(fd.precondition.get, env))

    // Creating the proof function invocation.
    val proofFunctionExpr = functionInvocation(proofFd, mapping.map(_._2) ++ Seq(preExpr, postExpr))
    reporter.debug("Proof function invocation: " + proofFunctionExpr)

    // Evaluating the proof function.
    val evaluatedTheorem = evaluator.eval(proofFunctionExpr) match {
      case Successful(CaseClass(ct, Seq(expr))) => {
        // The returned value should be of type theorem.
        assert(ct.classDef == library.Theorem.get)

        reporter.debug("Proof function " + proofFd.qualifiedName(vctx.program) +
          " evaluates to expression: " + expr)
        expr
      }
      case EvaluatorError(msg) => {
        reporter.fatalError(msg)
      }
      case RuntimeError(msg) => {
        reporter.fatalError(msg)
      }
    }

    // Converting back the encoded Expr to a PureScala Expr.
    def swap[A, B](t: (A, B)): (B, A) = (t._2, t._1)
    val backEnv: Map[Expr, Identifier] = mapping.map(swap).toMap
    val pureScalaTheorem = encoder.decodeExpr(evaluatedTheorem, backEnv)

    // Gettings the set of verification conditions from the evaluator.
    val proofVCs = evaluator.popVCExprs.map {
      case e: Expr => VC(encoder.decodeExpr(e, backEnv), proofFd, VCKinds.ProveInvocation).setPos(proofFd)
    }

    reporter.debug("Corresponding vcs : " + proofVCs.map(_.condition).mkString(", "))  

    // Creation of the VC that ensures that the proof implies the postcondition.
    val exprVC = implies(
      and(fd.precOrTrue, pureScalaTheorem),
      application(fd.postcondition.get, Seq(fd.body.get)))

    reporter.debug("Proof implication VC: " + exprVC)
    
    // Returning all VCs.
    VC(exprVC, fd, VCKinds.ProofImplication).setPos(fd) +: proofVCs
  }
}