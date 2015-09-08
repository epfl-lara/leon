package leon.solvers.isabelle

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import leon._
import leon.purescala.Definitions._
import leon.utils._
import leon.verification._

object IsabellePhase extends LeonPhase[Program, VerificationReport] {

  object IsabelleVC extends VCKind("Isabelle", "isa")

  val name = "isabelle"
  val description = "Isabelle verification"

  implicit val debugSection = DebugSectionIsabelle

  def run(context: LeonContext)(program: Program): VerificationReport = {
    val env = IsabelleEnvironment(context, program)

    val report = env.map { env =>
      def prove(fd: FunDef) = fd.statement.map { expr =>
        context.reporter.debug(s"Proving postcondition of ${fd.qualifiedName(program)} ...")
        val vc = VC(expr, fd, IsabelleVC).setPos(fd.getPos)
        val term = env.functions.term(expr)
        val input = term.map(t => (List(t), fd.proofMethod(vc, context)))
        val result = Await.result(input.flatMap(env.system.invoke(Prove)).assertSuccess(context), Duration.Inf) match {
          case Some(thm) => VCResult(VCStatus.Valid, None, None)
          case None => VCResult(VCStatus.Unknown, None, None)
        }
        vc -> Some(result)
      }

      VerificationReport(program, env.selectedFunDefs.flatMap(prove).toMap)
    }

    Await.result(report, Duration.Inf)
  }

}
