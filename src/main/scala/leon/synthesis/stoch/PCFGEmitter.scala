package leon
package synthesis
package stoch

import purescala.Common.{FreshIdentifier, Identifier}
import purescala.Constructors.tupleTypeWrap
import purescala.Definitions._
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

    /*
    type ExprConstrStats = Map[TypeTree, Map[Class[_ <: Expr], Map[Seq[TypeTree], Seq[Expr]]]]
    type FunctionCallStats = Map[TypeTree, Map[TypedFunDef, Seq[FunctionInvocation]]]
    type TypeStats = Map[TypeTree, Seq[Expr]]
    type LitStats = Map[TypeTree, Map[Any, Seq[Literal[_]]]]
    */

    def total1[K1, T](map: Map[K1, Seq[T]]) = map.values.flatten.size
    def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum

    val l1 = for {
      (tt, ttMap) <- ecs.toSeq.sortBy { case (tt, ttMap) => (-total2(ttMap), tt.toString) }
      typeTotal = total2(ttMap)
      (constr, ttConstrMap) <- ttMap.toList.sortBy { case (constr, ttConstrMap) => (-total1(ttConstrMap), constr.toString)}
      if constr != classOf[FunctionInvocation]
      (argTypes, exprs) <- ttConstrMap if exprs.nonEmpty
      production <- emit(canaryExprs, canaryTypes, tt, constr, argTypes, exprs, ecs, fcs, ls)
    } yield production

    val l2: Seq[FunDef] = for {
      (tt, ttMap) <- fcs.toSeq.sortBy { case (tt, ttMap) => (-total1(ttMap), tt.toString) }
      (tfd, fis) <- ttMap.toSeq.sortBy { case (tfd, fis) => (-fis.size, tfd.id.toString) }
      prodRule <- emitFunctionCalls(canaryExprs, canaryTypes, tt, tfd, fis, ecs, fcs, ls)
    } yield prodRule

    l1 ++ l2
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

    val suppressedConstrs: Set[Class[_ <: Expr]] = Set(classOf[Ensuring], classOf[Require], classOf[Let],
      classOf[Error], classOf[NoTree])

    if (suppressedConstrs.contains(constr)) Seq()
    else if ((constr == classOf[And] || constr == classOf[Or]) && argTypes.length != 2) Seq()
    else if ((constr == classOf[And] || constr == classOf[Or]) && argTypes.length == 2) {
      val exprsPrime = ecs(tt)(constr).values.flatten.toSeq
      emitGeneral(canaryExprs, canaryTypes, tt, constr, argTypes, exprsPrime, ecs, fcs, ls)
    }
    else if (exprs.head.isInstanceOf[Literal[_]]) {
      emitLiterals(canaryExprs, canaryTypes, tt, constr, argTypes, exprs, ecs, fcs, ls)
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
    val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
    val productionName: String = s"p${typeTreeName(tt)}$constrName"
    val id: Identifier = FreshIdentifier(productionName, tt)

    val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
    val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) => ValDef(FreshIdentifier(s"v$idx", ptt)) }
    val Operator(_, op) = exprs.head
    val fullBody: Expr = {
      if (constr == classOf[Variable]) {
        val FunctionInvocation(TypedFunDef(varfd, _), _) = canaryExprs.filter(_.isInstanceOf[FunctionInvocation])
          .map(_.asInstanceOf[FunctionInvocation])
          .filter(_.tfd.id.name.contains("variable"))
          .filter(_.tfd.tps.length == 1)
          .filter(_.args.isEmpty)
          .head
        val tfd = TypedFunDef(varfd, Seq(tt))
        FunctionInvocation(tfd, Seq())
      } else {
        op(params.map(_.toVariable))
      }
    }

    val production: FunDef = new FunDef(id, tparams, params, tt)
    production.fullBody = fullBody

    val frequency: Int = exprs.size
    production.addFlag(Annotation("production", Seq(Some(frequency))))

    Seq(production)
  }

  def emitLiterals(
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
    for ((value, literals) <- ls(tt).toSeq.sortBy(-_._2.size)) yield {
      val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
      val productionName: String = s"p${typeTreeName(tt)}$constrName"
      val id: Identifier = FreshIdentifier(productionName, tt)

      require(getTypeParams(FunctionType(argTypes, tt)).isEmpty) // Literals cannot be of generic type, can they?
      val tparams: Seq[TypeParameterDef] = Seq()
      require(argTypes.isEmpty) // Literals cannot have arguments, can they?
      val params: Seq[ValDef] = Seq()
      val fullBody: Expr = literals.head

      val production: FunDef = new FunDef(id, tparams, params, tt)
      production.fullBody = fullBody

      val frequency: Int = literals.size
      production.addFlag(Annotation("production", Seq(Some(frequency))))

      production
    }
  }

  def emitFunctionCalls(
                   canaryExprs: Seq[Expr],
                   canaryTypes: Map[String, TypeTree],
                   tt: TypeTree,
                   tfd: TypedFunDef,
                   fis: Seq[FunctionInvocation],
                   ecs: ExprConstrStats,
                   fcs: FunctionCallStats,
                   ls: LitStats
                 ): Seq[FunDef] = {
    if (tfd.getPos.file.toString.contains("/leon/library/leon/")) {
      val productionName: String = s"p${typeTreeName(tt)}FunctionInvocation${tfd.id.name}"
      val id: Identifier = FreshIdentifier(productionName, tt)

      val argTypes = tfd.params.map(_.getType)
      val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
      val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) => ValDef(FreshIdentifier(s"v$idx", ptt)) }
      val fullBody: Expr = FunctionInvocation(tfd, params.map(_.toVariable))

      val production: FunDef = new FunDef(id, tparams, params, tt)
      production.fullBody = fullBody

      val frequency: Int = fis.size
      production.addFlag(Annotation("production", Seq(Some(frequency))))

      Seq(production)
    } else {
      // Ignore calls to non-library functions
      Seq()
    }
  }

  def typeTreeName(tt: TypeTree): String = tt match {
    case FunctionType(from, to) => s"${typeTreeName(tupleTypeWrap(from))}_${typeTreeName(to)}_Arrow"
    case TupleType(bases) => bases.map(typeTreeName).mkString("", "_", s"_Tuple${bases.size}")
    case SetType(base) => s"${typeTreeName(base)}_Set"
    case classTT: ClassType =>
      if (classTT.tps.isEmpty) classTT.toString else classTT.tps.mkString("", "_", "_" + classTT.classDef.id.name)
    case _ => tt.toString
  }

}
