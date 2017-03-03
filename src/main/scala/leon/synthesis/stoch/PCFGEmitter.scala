package leon
package synthesis
package stoch

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.{Annotation, FunDef, ValDef}
import leon.purescala.Expressions._
import leon.purescala.Extractors.Operator
import leon.purescala.Types._
import leon.synthesis.stoch.Stats.ExprConstrStats

object PCFGEmitter {

  // type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Seq[Expr]]]
  def emit(allTypes: Set[TypeTree], stats: ExprConstrStats): Seq[FunDef] = {
    for {
      tt <- stats.keys.toSeq
      constr <- stats(tt).keys
      fd <- emit(allTypes, tt, constr, stats)
    } yield fd
  }

  def emit(allTypes: Set[TypeTree], tt: TypeTree, constr: Class[_ <: Expr], stats: ExprConstrStats): Seq[FunDef] = {
    require(stats.contains(tt) && stats(tt).contains(constr))

    // if (constr == classOf[Equals]) ... // TODO! Put special cases here
    // else { ... }

    // TODO! Variables!

    val es = stats(tt)(constr)
    val freq = es.size

    /* if (constr == classOf[Variable]) {
      val funName = FreshIdentifier("var", tt)
      val funDef = new FunDef(funName, Seq(), Seq(), tt)
      // funDef.fullBody = ??? // "variable[tt]" // TODO!
      funDef.addFlag(Annotation("production", Seq(Some(freq))))
      Seq(funDef)
    } else if (constr == classOf[Ensuring]) {
      Seq() // TODO!
    } else {
      val esOpTypes = es map { case e @ Operator(ops, _) => ops.map(_.getType) }
      val typeSign = esOpTypes.groupBy(ts => ts).mapValues(_.size).toSeq.sortBy(-_._2).head._1
      val builder = es.collectFirst { case Operator(ops, b) if typeSign == ops.map(_.getType) => b }.get

      val funName = FreshIdentifier(constr.toString, tt)
      val args = typeSign.zipWithIndex.map { case (argType, index) => ValDef(FreshIdentifier(s"arg$index", argType)) }
      val funDef = new FunDef(funName, Seq(), args, tt)
      funDef.fullBody = builder(args.map(_.toVariable))
      funDef.addFlag(Annotation("production", Seq(Some(freq))))
      Seq(funDef)
    } */

    /* if (constr == classOf[And]) {
      require(tt == BooleanType)
      val funName = FreshIdentifier("and", BooleanType)
      val arg1 = ValDef(FreshIdentifier("arg1", BooleanType))
      val arg2 = ValDef(FreshIdentifier("arg2", BooleanType))
      val funDef = new FunDef(funName, Seq(), Seq(arg1, arg2), BooleanType)
      funDef.fullBody = And(arg1.toVariable, arg2.toVariable)
      funDef.addFlag(Annotation("production", Seq(Some(freq))))
            .addFlag(Annotation("commutative", Seq()))
      Seq(funDef)
    } else {
      Seq() // ???
    } */

    ???
  }

}
