package leon
package synthesis
package stoch

import purescala.Common.{FreshIdentifier, Identifier}
import purescala.Constructors.tupleTypeWrap
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors.Operator
import purescala.Types._
import purescala.{TypeOps => TO}
import Stats.{ExprConstrStats, FunctionCallStats, LitStats}
import StatsUtils._
import leon.utils.Position

object PCFGEmitter {

  def emit(
            program: Program,
            ecs: ExprConstrStats,
            fcs: FunctionCallStats,
            ls: LitStats
          ): UnitDef = {

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
      (constr, ttConstrMap) <- ttMap.toList.sortBy { case (constr, ttConstrMap) => (-total1(ttConstrMap), constr.toString) }
      if constr != classOf[FunctionInvocation]
      (argTypes, exprs) <- ttConstrMap if exprs.nonEmpty
      production <- emit(program, tt, constr, argTypes, exprs, ls)
    } yield production

    val l2: Seq[FunDef] = for {
      (tt, ttMap) <- fcs.toSeq.sortBy { case (tt, ttMap) => (-total1(ttMap), tt.toString) }
      (pos, fis) <- ttMap.toSeq.sortBy { case (pos, fis) => (-fis.size, pos) }
      prodRule <- emitFunctionCalls(tt, pos, fis)
    } yield prodRule

    val moduleDef = ModuleDef(FreshIdentifier("grammar"), l1 ++ l2, isPackageObject = false)
    val packageRef = List("leon", "grammar")
    val imports = List(
                        Import(List("leon", "collection"), isWild = true),
                        Import(List("leon", "lang"), isWild = true),
                        Import(List("leon", "lang", "synthesis"), isWild = true),
                        Import(List("leon", "math"), isWild = true),
                        Import(List("annotation", "grammar"), isWild = true)
                      )
    new UnitDef(FreshIdentifier("grammar"), packageRef, imports, Seq(moduleDef), isMainUnit = true)
  }

  def emit(
            program: Program,
            tt: TypeTree,
            constr: Class[_ <: Expr],
            argTypes: Seq[TypeTree],
            exprs: Seq[Expr],
            ls: LitStats
          ): Seq[FunDef] = {

    if (exprs.head.isInstanceOf[Literal[_]])
      emitLiterals(tt, constr, ls)
    else if (constr == classOf[CaseClass])
      emitCaseClass(tt, constr, argTypes, exprs)
    else emitGeneral(program, tt, constr, argTypes, exprs)

  }

  def emitCaseClass(
    tt: TypeTree,
    constr: Class[_ <: Expr],
    argTypes: Seq[TypeTree],
    exprs: Seq[Expr]
  ): Seq[FunDef] = {
    val conCounts = exprs.map(_.asInstanceOf[CaseClass]).groupBy(e => normalizeType(e.ct, false).asInstanceOf[CaseClassType]).mapValues(_.size).toSeq
    conCounts map { case (cct, frequency) =>
      val cd = cct.classDef
      val constrName = cd.id.name
      val productionName: String = s"p${typeTreeName(tt)}$constrName"
      val id: Identifier = FreshIdentifier(productionName, tt)

      val tparams: Seq[TypeParameterDef] = getTypeParams(cct) map TypeParameterDef
      val params: Seq[ValDef] = cct.fields.map(f => ValDef(f.id.freshen))

      val fullBody = CaseClass(cct, params map (_.toVariable))

      val tinst = tt.asInstanceOf[ClassType].classDef.typed(cct.tps)

      val production: FunDef = new FunDef(id, tparams, params, tinst)
      production.fullBody = fullBody

      production.addFlag(Annotation("production", Seq(Some(frequency))))

      production
    }
  }

  def emitGeneral(
    program: Program,
    tt: TypeTree,
    constr: Class[_ <: Expr],
    argTypes: Seq[TypeTree],
    exprs: Seq[Expr]
  ): Seq[FunDef] = {
    val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
    val productionName: String = s"p${typeTreeName(tt)}$constrName"
    val id: Identifier = FreshIdentifier(productionName, tt)

    val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
    val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) => ValDef(FreshIdentifier(s"v$idx", ptt)) }
    val modelExpr = exprs.head
    val typeN = TO.instantiation_<:(modelExpr.getType, tt).get
    val modelExprInst = TO.instantiateType(modelExpr, typeN, Map())
    val Operator(_, op) = modelExprInst
    val fullBody: Expr = {
      if (constr == classOf[Variable]) {
        val tfd = TypedFunDef(program.library.variable.get, Seq(tt))
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
                   tt: TypeTree,
                   constr: Class[_ <: Expr],
                   ls: LitStats
                 ): Seq[FunDef] = {
    for ((_, literals) <- ls(tt).toSeq.sortBy(-_._2.size)) yield {
      val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
      val productionName: String = s"p${typeTreeName(tt)}$constrName"
      val id: Identifier = FreshIdentifier(productionName, tt)
      val params: Seq[ValDef] = Seq()
      val fullBody: Expr = literals.head

      val production: FunDef = new FunDef(id, Seq(), params, tt)
      production.fullBody = fullBody

      val frequency: Int = literals.size
      production.addFlag(Annotation("production", Seq(Some(frequency))))

      production
    }
  }

  def emitFunctionCalls(tt: TypeTree, pos: Position, fis: Seq[FunctionInvocation]): Seq[FunDef] = {
    if (pos.file.toString.contains("/leon/library/leon/")) {
      val tfd = fis.head.tfd
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
