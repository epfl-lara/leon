package leon
package synthesis

import purescala.Types._
import purescala.Expressions._
import purescala.Definitions._
import purescala.TypeOps._


class FunctionCallsFinder(types: Set[TypeTree])  {

  def find(fd: FunDef, returnType: TypeTree): Traversable[TypedFunDef] = {

    instantiation_<:(fd.returnType, returnType) match {
      case Some(tmap0) =>
        val free = fd.tparams.map(_.tp) diff tmap0.keySet.toSeq;

        val tmaps = if (free.nonEmpty) {
          // Instantiate type parameters not constrained by the return value
          // of `fd`
          //
          // e.g.:
          // def countFilter[T](x: List[T], y: T => Boolean): BigInt
          //
          // We try to find instantiation of T such that arguments have
          // candidates
          //

          // Step 1. We identify the type patterns we need to match:
          // e.g. (List[T], T => Boolean)
          val pattern0 = fd.params.map(_.getType).distinct

          // Step 2. We use the set of interesting types to fill our pattern
          def discover(free: TypeParameter, fixed: Set[Map[TypeParameter, TypeTree]]): Set[Map[TypeParameter, TypeTree]] = {
            for {
              map0 <- fixed
              p1 = pattern0.map(instantiateType(_, map0))
              p <- p1
              t <- types
              map1 <- unify(p, t, Seq(free))
            } yield {
              map0 ++ map1
            }
          }

          var tmaps = Set(tmap0)

          for (f <- free) {
            tmaps = discover(f, tmaps)
          }

          tmaps
        } else {
          List(tmap0)
        }

        for (tmap <- tmaps) yield {
          fd.typed(fd.tparams.map(tpd => tmap.getOrElse(tpd.tp, tpd.tp)))
        }

      case None =>
        Nil
    }
  }
}
