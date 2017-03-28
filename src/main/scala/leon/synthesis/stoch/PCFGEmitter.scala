package leon
package synthesis
package stoch

import purescala.Common.{FreshIdentifier, Identifier}
import purescala.Constructors.tupleTypeWrap
import purescala.Definitions.{Annotation, FunDef, TypeParameterDef, ValDef}
import purescala.Expressions._
import purescala.Extractors.Operator
import purescala.Types._
import Stats.{ExprConstrStats, FunctionCallStats, LitStats}
import StatsUtils.getTypeParams

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
    if (constr == classOf[Ensuring]) Seq()
    else if ((constr == classOf[And] || constr == classOf[Or]) && argTypes.length != 2) Seq()
    else if ((constr == classOf[And] || constr == classOf[Or]) && argTypes.length == 2) {
      val exprsPrime = ecs(tt)(constr).values.flatten.toSeq
      emitGeneral(canaryExprs, canaryTypes, tt, constr, argTypes, exprsPrime, ecs, fcs, ls)
    }
    else emitGeneral(canaryExprs, canaryTypes, tt, constr, argTypes, exprs, ecs, fcs, ls)
  }

  def emitGeneral(
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
    val productionName: String = s"p${typeTreeName(tt)}$constrName"
    val id: Identifier = FreshIdentifier(productionName, tt)

    val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
    val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) => ValDef(FreshIdentifier(s"v$idx", ptt)) }
    val Operator(_, op) = exprs.head
    val fullBody: Expr = op(params.map(_.toVariable))

    val production: FunDef = new FunDef(id, tparams, params, tt)
    production.fullBody = fullBody

    val frequency: Int = exprs.size
    production.addFlag(Annotation("production", Seq(Some(frequency))))

    Seq(production)
  }

  def typeTreeName(tt: TypeTree): String = tt match {
    case FunctionType(from, to) => s"${typeTreeName(tupleTypeWrap(from))}_${typeTreeName(to)}_Arrow"
    case TupleType(bases) => bases.map(typeTreeName).mkString("", "_", s"_Tuple${bases.size}")
    case SetType(base) => s"${typeTreeName(base)}_Set"
    case classTT: ClassType =>
      if (classTT.tps.isEmpty) classTT.toString else classTT.tps.mkString("", "_", "_" + classTT.classDef.id.name)
    case _ => tt.toString
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
