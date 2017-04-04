package leon.synthesis.stoch

import leon.purescala.Common.{FreshIdentifier, Identifier}
import leon.purescala.Definitions._
import leon.purescala.Expressions.{And, Expr, Or}
import leon.purescala.Types.TypeTree
import leon.synthesis.stoch.Stats._
import leon.synthesis.stoch.StatsUtils.getTypeParams
import leon.utils.Position

object PCFG2Emitter {

  def total1[K1, T](map: Map[K1, Seq[T]]) = map.values.flatten.size
  def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum
  def total3[K1, K2, K3, T](map: Map[K1, Map[K2, Map[K3, Seq[T]]]]): Int = map.values.map(total2).sum

  def emit2(
            canaryExprs: Seq[Expr],
            canaryTypes: Map[String, TypeTree],
            ecs1: ExprConstrStats,
            fcs1: FunctionCallStats,
            ls1: LitStats,
            ecs2: ECS2,
            fcs2: FCS2,
            ls2: LS2
          ): (Seq[ClassDef], Seq[FunDef]) = {

    val implicits =
      for ((tt, ttS2) <- ecs2)
      yield {
        val ttImplicits =
          for ((idxPar, _) <- ttS2)
          yield {
            val labelName: String = idxPar match {
              case Some((idx, par)) =>
                val parName = par.toString.stripPrefix("class leon.purescala.Expressions$")
                s"${PCFGEmitter.typeTreeName(tt)}_${idx}_$parName"
              case None => s"${PCFGEmitter.typeTreeName(tt)}_None"
            }
            val labelId: Identifier = FreshIdentifier(labelName)
            val cd: CaseClassDef = new CaseClassDef(labelId, getTypeParams(tt).map(TypeParameterDef), None, false)
            cd.setFields(Seq(ValDef(FreshIdentifier("v", tt))))

            // cd.addFlag(IsImplicit)
            cd.addFlag(Annotation("label", Seq()))

            idxPar -> cd
          }
        tt -> ttImplicits
      }

    val labels = implicits.values.flatMap(_.values).toSeq
    (labels, Seq())

  }

}
