/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Path
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.Common._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Definitions.FunDef
import Witnesses._

/** Defines a synthesis triple of the form:
  * ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧
  * 
  * @param as The list of input identifiers so far
  * @param ws The axioms and other already proven theorems
  * @param pc The path condition so far
  * @param phi The formula on `as` and `xs` to satisfy
  * @param xs The list of output identifiers for which we want to compute a function
  */
case class Problem(as: List[Identifier], ws: Expr, pc: Path, phi: Expr, xs: List[Identifier], eb: ExamplesBank = ExamplesBank.empty) extends Printable {

  def inType  = tupleTypeWrap(as.map(_.getType))
  def outType = tupleTypeWrap(xs.map(_.getType))

  def allAs = as ++ pc.bindings.map(_._1)

  def asString(implicit ctx: LeonContext): String = {
    val pcws = pc withCond ws

    val ebInfo = "/"+eb.valids.size+","+eb.invalids.size+"/"

    s"""|⟦  ${if (as.nonEmpty) as.map(_.asString).mkString(", ") else "()"}
        |   ${pcws.toClause.asString} ≺
        |   ⟨ ${phi.asString} ⟩ 
        |   ${if (xs.nonEmpty) xs.map(_.asString).mkString(", ") else "()"}
        |⟧  $ebInfo""".stripMargin
  }

  def withWs(es: Seq[Expr]) = {
    val TopLevelAnds(prev) = ws
    copy(ws = andJoin(prev ++ es))
  }

  // Qualified example bank, allows us to perform operations (e.g. filter) with expressions
  def qeb(implicit sctx: SearchContext) = QualifiedExamplesBank(this.as, this.xs, eb)

}

object Problem {
  def fromSpec(
    spec: Expr,
    pc: Path = Path.empty,
    eb: ExamplesBank = ExamplesBank.empty,
    fd: Option[FunDef] = None
  ): Problem = {
    val xs = {
      val tps = spec.getType.asInstanceOf[FunctionType].from
      tps map (FreshIdentifier("x", _, alwaysShowUniqueID = true))
    }.toList

    val phi = application(simplifyLets(spec), xs map { _.toVariable})
    val as = (variablesOf(phi) ++ pc.variables -- xs).toList.sortBy(_.name)

    val sortedAs = fd match {
      case None => as
      case Some(fd) =>
        val argsIndex = fd.params.map(_.id).zipWithIndex.toMap.withDefaultValue(100)
        as.sortBy(a => argsIndex(a))
    }

    val (pcs, wss) = pc.partition {
      case w: Witness => false
      case _ => true
    }

    Problem(sortedAs, andJoin(wss), pcs, phi, xs, eb)
  }

}
