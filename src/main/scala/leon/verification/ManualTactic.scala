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

class ManualTactic(vctx: VerificationContext) extends DefaultTactic(vctx) {
  import vctx.reporter

  val library = Library(vctx.program)

  override val description = "Manual proof verification condition generation approach"

  override def generatePostconditions(fd: FunDef): Seq[VC] = {

    // Handling the case when the function has not post-condition.
    if (!fd.hasPostcondition) {
      reporter.warning("Function " + fd.qualifiedName(vctx.program) + " has no postcondition.")
      return Seq()
    }

    assert(fd.hasBody)

    // Getting the name of the proof from the annotation.
    val optProofName = for {
      optArgs <- fd.extAnnotations.get("manual")
      optFirstArg <- optArgs.headOption
      firstArg <- optFirstArg
      if firstArg.isInstanceOf[String]
    } yield firstArg.asInstanceOf[String]

    // Handling the case when the proof name is not specified.
    if (optProofName.isEmpty) {
      val errorMsg = "Proof function not specified in the @manual annotation of " + fd.qualifiedName(vctx.program) + "."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    val proofName = optProofName.get

    val optProofFd = vctx.program.lookupFunDef(proofName)

    // Handling the case when the proof function can not be found.
    if (optProofFd.isEmpty) {
      val errorMsg = "Proof function not found for " + fd.qualifiedName(vctx.program) + "."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    val proofFd = optProofFd.get

    // Handling the case when the proof function does not have the @proof annotation.
    if (!proofFd.annotations.contains("proof")) {
      val errorMsg = "Proof function of " + 
        fd.qualifiedName(vctx.program) + ", " + 
        proofFd.qualifiedName(vctx.program) +
        ", does not have the @proof annotation."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    // Verification of the signature of the proof function.
    checkSignature(fd, proofFd)

    val vcs = generateProofVCs(fd, proofFd)

    vcs
  }

  def checkSignature(fd: FunDef, proofFd: FunDef): Unit = {
    
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
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    // The first n parameters should all be of type Identifier.
    for (i <- 0 until n) {
      if (proofFdParams(i).getType != identifierType) {
        val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
          " should take a leon.theorem.Identifier as its argument at position " + (i + 1) + "."
        reporter.error(errorMsg)
        throw new Exception(errorMsg)
      }
    }

    // The next parameters should be the precondition, of type Theorem.
    if (proofFdParams(n).getType != theoremType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a precondition leon.theorem.Theorem as second-last argument."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    // The last parameter should be the post condition, of type Term.
    if (proofFdParams(n + 1).getType != termType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a postcondition leon.theorem.Term as last argument."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    // The return type should be a Theorem.
    if (proofFd.returnType != theoremType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should return a value of type leon.theorem.Theorem."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }
  }

  def generateProofVCs(fd: FunDef, proofFd: FunDef): Seq[VC] = {

    val encoder = new ExprEncoder(vctx)
    val evaluator = new ProofEvaluator(vctx, vctx.program)

    reporter.info("Starting execution of the proof function " + proofFd.qualifiedName(vctx.program))

    val mapping = for (vd <- fd.params) yield (vd.id -> encoder.makeIdentifier(vd.id.uniqueName))

    val env: Map[Identifier, Expr] = mapping.toMap

    val postExpr = encoder.encodeExpr(application(fd.postcondition.get, Seq(fd.body.get)), env)
    val preExpr = encoder.caseClass(library.Theorem, encoder.encodeExpr(fd.precondition.get, env))

    val proofFunctionExpr = functionInvocation(proofFd, mapping.map(_._2) ++ Seq(preExpr, postExpr))
    println(proofFunctionExpr)

    val evaluatedTheorem = evaluator.eval(proofFunctionExpr) match {
      case Successful(CaseClass(_, Seq(expr))) => {
        reporter.info("Proof function " + proofFd.qualifiedName(vctx.program) +
          " evaluates to expression: " + expr)
        expr
      }
      case EvaluatorError(msg) => {
        reporter.error(msg)
        throw new Exception(msg)
      }
      case RuntimeError(msg) => {
        reporter.error(msg)
        throw new Exception(msg)
      }
    }

    def swap[A, B](t: (A, B)): (B, A) = (t._2, t._1)

    val backEnv: Map[Expr, Identifier] = mapping.map(swap).toMap
    val pureScalaTheorem = encoder.decodeExpr(evaluatedTheorem, backEnv)

    val proofVCs = evaluator.getVCExprs.map {
      case e: Expr => VC(encoder.decodeExpr(e, backEnv), fd, VCKinds.ProveInvocation).setPos(proofFd)
    }

    reporter.info("Corresponding vcs : " + proofVCs.map(_.condition))  

    val exprVC = implies(
      and(fd.precOrTrue, pureScalaTheorem),
      application(fd.postcondition.get, Seq(fd.body.get)))
    
    VC(exprVC, fd, VCKinds.ProofImplication).setPos(fd) +: proofVCs
  }
}