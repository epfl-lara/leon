/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._

class ManualTactic(vctx: VerificationContext) extends DefaultTactic(vctx) {
  override val description = "Manual proof verification condition generation approach"

  override def generatePostconditions(fd: FunDef): Seq[VC] = {

    import vctx.reporter

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

    Seq()
  }
}