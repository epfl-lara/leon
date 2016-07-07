/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Types._

class ManualTactic(vctx: VerificationContext) extends DefaultTactic(vctx) {
  import vctx.reporter

  override val description = "Manual proof verification condition generation approach"

  override def generatePostconditions(fd: FunDef): Seq[VC] = {

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

    Seq()
  }

  def checkSignature(fd: FunDef, proofFd: FunDef): Unit = {
    
    // Resolving the type of Theorem.
    val optTheoremClass = vctx.program.lookupCaseClass("leon.theorem.Theorem")
    if (optTheoremClass.isEmpty) {
      throw new Exception("Case class leon.theorem.Theorem not found.")
    }
    val theoremType = CaseClassType(optTheoremClass.get, Seq())

    // Resolving the type of Identifier.
    val optIdentifierClass = vctx.program.lookupCaseClass("leon.theorem.Identifier")
    if (optIdentifierClass.isEmpty) {
      throw new Exception("Case class leon.theorem.Identifier not found.")
    }
    val identifierType = CaseClassType(optIdentifierClass.get, Seq())

    // Resolving the type of Formula.
    val optFormulaClass = vctx.program.lookupAbstractClass("leon.theorem.Formula")
    if (optFormulaClass.isEmpty) {
      throw new Exception("Abstract class leon.theorem.Formula not found.")
    }
    val formulaType = AbstractClassType(optFormulaClass.get, Seq())

    val fdParams = fd.params
    val proofFdParams = proofFd.params

    if (proofFdParams.size != fdParams.size + 2) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) + 
        " has wrong number of parameters."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    val n = fdParams.size

    for (i <- 0 until n) {
      if (proofFdParams(i).getType != identifierType) {
        val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
          " should take a leon.theorem.Identifier as its argument at position " + (i + 1) + "."
        reporter.error(errorMsg)
        throw new Exception(errorMsg)
      }
    }

    if (proofFdParams(n).getType != theoremType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a precondition leon.theorem.Theorem as second-last argument."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    if (proofFdParams(n + 1).getType != formulaType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a postcondition leon.theorem.Formula as last argument."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }

    if (proofFd.returnType != theoremType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should return a value of type leon.theorem.Theorem."
      reporter.error(errorMsg)
      throw new Exception(errorMsg)
    }
  }
}