/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Types._
import utils.Library

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
    val library = Library(vctx.program)
    
    val theoremType = CaseClassType(library.Theorem.get, Seq())
    val identifierType = CaseClassType(library.Identifier.get, Seq())
    val formulaType = AbstractClassType(library.Formula.get, Seq())

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

    // The last parameter should be the post condition, of type Formula.
    if (proofFdParams(n + 1).getType != formulaType) {
      val errorMsg = "Proof function " + proofFd.qualifiedName(vctx.program) +
        " should take a postcondition leon.theorem.Formula as last argument."
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
}