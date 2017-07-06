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
  val imports = List(
    Import(List("leon", "collection"), isWild = true),
    Import(List("leon", "collection", "List"), isWild = true),
    Import(List("leon", "collection", "ListOps"), isWild = true),
    Import(List("leon", "collection", "ListSpecs"), isWild = true),
    Import(List("leon", "lang", "Set"), isWild = true),
    Import(List("leon", "lang"), isWild = true),
    Import(List("leon", "lang"), isWild = true),
    Import(List("leon", "lang", "synthesis"), isWild = true),
    Import(List("leon", "math"), isWild = true),
    Import(List("annotation", "grammar"), isWild = true)
  )

  val libFiles = Set(
    "/library/leon/collection/List",
    "/library/leon/lang/package",
    "/library/leon/lang/Set"
  )

  def exclude(fd: FunDef) = {
    fd.flags.contains(IsPrivate) ||
    (fd.postcondition match {
      case Some(Lambda(_, BooleanLiteral(true))) => true
      case _ => false
    })
  }

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
      production <- emitSingle(program, tt, constr, argTypes, exprs, ls)
    } yield production

    val l2: Seq[FunDef] = for {
      (tt, ttMap) <- fcs.toSeq.sortBy { case (tt, ttMap) => (-total1(ttMap), tt.toString) }
      (pos, fis) <- ttMap.toSeq.sortBy { case (pos, fis) => (-fis.size, pos) }
      prodRule <- emitFunctionCalls(tt, pos, fis)
    } yield prodRule

    val moduleDef = ModuleDef(FreshIdentifier("grammar"), l1 ++ l2, isPackageObject = false)
    val packageRef = List("leon", "grammar")
    new UnitDef(FreshIdentifier("grammar"), packageRef, imports, Seq(moduleDef), isMainUnit = true)
  }

  def emitSingle(
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
      production.addFlag(Annotation("tag", Seq(Some("top"))))

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
    def tagOf = Map[Class[_ <: Expr], String](
      classOf[BooleanLiteral] -> "booleanC",
      classOf[InfiniteIntegerLiteral] -> "const",
      classOf[IntLiteral] -> "const",
      classOf[And] -> "and",
      classOf[Or] -> "or",
      classOf[Not] -> "not",
      classOf[Plus] -> "plus",
      classOf[BVPlus] -> "plus",
      classOf[Minus] -> "minus",
      classOf[BVMinus] -> "minus",
      classOf[Times] -> "times",
      classOf[BVTimes] -> "times",
      classOf[Modulo] -> "mod",
      classOf[Division] -> "div",
      classOf[Equals] -> "equals",
      classOf[IfExpr] -> "ite"
    ).withDefaultValue("top")

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
    production.addFlag(Annotation("tag", Seq(Some(tagOf(constr)))))

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
      val id: Identifier = FreshIdentifier(productionName, tt, true)
      val params: Seq[ValDef] = Seq()
      val lit = literals.head
      val fullBody: Expr = lit

      val production: FunDef = new FunDef(id, Seq(), params, tt)
      production.fullBody = fullBody

      val frequency: Int = literals.size
      val tag = lit match {
        case BooleanLiteral(_) => "booleanC"
        case InfiniteIntegerLiteral(z) if z == BigInt(0) => "0"
        case InfiniteIntegerLiteral(o) if o == BigInt(1) => "1"
        case IntLiteral(0) => "0"
        case IntLiteral(1) => "1"
        case _ => "const"
      }

      production.addFlag(Annotation("production", Seq(Some(frequency))))
      production.addFlag(Annotation("tag", Seq(Some(tag))))

      production
    }
  }

  def emitFunctionCalls(tt: TypeTree, pos: Position, fis: Seq[FunctionInvocation]): Seq[FunDef] = {
    if (Stats2Main.REPAIR){
      if (pos.file.toString.contains("library/leon")) return Seq()
    } else {
      if (!libFiles.exists(pos.file.toString.contains)) return Seq() // Ignore non-lib calls
    }
    val tfd = fis.head.tfd
    if (exclude(tfd.fd)) return Seq() // exclude some functions
    val tmap = TO.instantiation_<:(tfd.returnType, tt).get
    val argTypes = tfd.params.map(_.getType).map(TO.instantiateType(_, tmap))
    val retType = tt

    val params = argTypes.zipWithIndex.map { case (tp, ind) => ValDef(FreshIdentifier(s"v$ind", tp)) }

    val tparams = getTypeParams(FunctionType(argTypes, retType)).map(TypeParameterDef)

    val id = FreshIdentifier("fd", retType, true)

    val fd = new FunDef(id, tparams, params, retType)

    val invocationTps = tfd.tps.map(TO.instantiateType(_, tmap))

    val fullBody = FunctionInvocation(
      tfd.fd.typed(invocationTps),
      params map (_.toVariable)
    )

    fd.fullBody = fullBody
    fd.addFlag(Annotation("tag", Seq(Some("top"))))
    fd.addFlag(Annotation("production", Seq(Some(fis.size))))
    Seq(fd)
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
