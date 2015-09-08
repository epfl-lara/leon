package leon.solvers.isabelle

import leon._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.DefOps
import leon.purescala.Expressions._
import leon.purescala.TypeOps
import leon.purescala.Types._
import leon.utils._

object AdaptationPhase extends TransformationPhase {

  val name = "adaptation"
  val description = "Function parameter adaptation"

  implicit val debugSection = DebugSectionIsabelle

  def apply(context: LeonContext, program: Program): Program = {
    val dummy = program.library.Dummy match {
      case Some(dummy) => dummy
      case None => context.reporter.internalError("Definition of dummy type not found")
    }

    def mkDummyTyp(tp: TypeParameter) =
      CaseClassType(dummy, List(tp))

    def mkDummyParameter(tp: TypeParameter) =
      ValDef(FreshIdentifier("dummy", mkDummyTyp(tp)), Some(mkDummyTyp(tp)))

    def mkDummyArgument(tree: TypeTree) =
      CaseClass(CaseClassType(dummy, List(tree)), Nil)

    val enabled =
      context.findOptionOrDefault(SharedOptions.optSelectedSolvers).contains("isabelle") ||
      context.findOptionOrDefault(Main.MainComponent.optIsabelle)

    if (!enabled) program
    else {
      context.reporter.debug("Running adaptation phase, because Isabelle is selected ...")

      val map = program.definedFunctions.flatMap { fd =>
        val expected = fd.tparams.map(_.tp).toSet
        val actual = fd.params.map(_.getType).flatMap(TypeOps.typeParamsOf).toSet ++ TypeOps.typeParamsOf(fd.returnType).toSet
        if (expected == actual)
          None
        else {
          val diff: List[TypeParameter] = (expected -- actual).toList
          context.reporter.debug(s"Rewriting function definition ${fd.qualifiedName(program)}: adding dummies for hidden type parameter(s) ${diff.map(_.id).mkString(" and ")}")
          val nid = FreshIdentifier(fd.id.name, FunctionType(fd.params.map(_.getType) ++ diff.map(mkDummyTyp), fd.returnType))
          val nfd = new FunDef(nid, fd.tparams, fd.returnType, fd.params ++ diff.map(mkDummyParameter))
          nfd.copyContentFrom(fd)
          nfd.setPos(fd.getPos)
          Some(fd -> ((nfd, diff)))
        }
      }.toMap

      def mapFunDef(fd: FunDef): Option[FunDef] = map.get(fd).map(_._1)

      def mapFunInvocation(fi: FunctionInvocation, nfd: FunDef): Option[Expr] = map.get(fi.tfd.fd).map { case (_, diff) =>
        val inst = (nfd.tparams.map(_.tp) zip fi.tfd.tps).toMap
        val args = diff.map(t => mkDummyArgument(inst(t)))
        FunctionInvocation(nfd.typed(fi.tfd.tps), fi.args ++ args)
      }

      DefOps.replaceFunDefs(program)(mapFunDef, mapFunInvocation)._1
    }
  }

}
