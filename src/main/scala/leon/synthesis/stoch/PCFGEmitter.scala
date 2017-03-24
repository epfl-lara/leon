package leon
package synthesis
package stoch

import leon.purescala.Common.{FreshIdentifier, Identifier}
import leon.purescala.Definitions.{Annotation, FunDef, TypeParameterDef, ValDef}
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.synthesis.stoch.Stats.{ExprConstrStats, FunctionCallStats, LitStats, TypeStats}

object PCFGEmitter {

  def emit(
            canaryExprs: Seq[Expr],
            canaryTypes: Map[String, TypeTree],
            ecs: ExprConstrStats,
            fcs: FunctionCallStats,
            ls: LitStats
          ): Seq[FunDef] = {

    def total1[K1, T](map: Map[K1, Seq[T]]) = map.values.flatten.size
    def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum

    for {
      (tt, ttMap) <- ecs.toList.sortBy { case (tt, ttMap) => (-total2(ttMap), tt.toString) }
      typeTotal = total2(ttMap)
      (constr, ttConstrMap) <- ttMap.toList.sortBy { case (constr, ttConstrMap) => (-total1(ttConstrMap), constr.toString)}
      (argTypes, exprs) <- ttConstrMap if exprs.nonEmpty
      production <- emit(canaryExprs, canaryTypes, tt, constr, argTypes, exprs, ecs, fcs, ls)
    } yield production

  }

  def emit(
            canaryExprs: Seq[Expr],
            canaryTypes: Map[String, TypeTree],
            tt: TypeTree,
            constr: Class[_ <: Expr],
            argTypes: Seq[TypeTree],
            exprs: Seq[Expr],
            ecs: ExprConstrStats,
            fcs: FunctionCallStats,
            ls: LitStats
          ): Seq[FunDef] = {
    /*
    type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]
    type FunctionCallStats = Map[TypeTree, Map[TypedFunDef, Seq[FunctionInvocation]]]
    type TypeStats = Map[TypeTree, Seq[Expr]]
    type LitStats = Map[TypeTree, Map[Any, Seq[Literal[_]]]]
    */

    val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
    val productionName: String = s"p$tt$constrName"
    val id: Identifier = FreshIdentifier(productionName, tt)

    val tparams: Seq[TypeParameterDef] = Seq() // TODO!
    val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (tt, idx) => ValDef(FreshIdentifier(s"v$idx", tt)) }
    val fullBody: Expr = null // TODO!

    val production: FunDef = new FunDef(id, tparams, params, tt)
    production.fullBody = fullBody

    val frequency: Int = exprs.size
    production.addFlag(new Annotation("production", Seq(Some(frequency))))

    Seq(production)
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
