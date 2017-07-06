package leon.synthesis.stoch

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Extractors.Operator
import leon.purescala.Constructors.caseClassSelector
import leon.purescala.Types._
import leon.purescala.{TypeOps => TO}
import leon.synthesis.stoch.Stats._
import leon.synthesis.stoch.StatsUtils._
import leon.utils.Position

object PCFG2Emitter {

  def total1[K1, T](map: Map[K1, Seq[T]]): Int = map.values.flatten.size
  def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum
  def total3[K1, K2, K3, T](map: Map[K1, Map[K2, Map[K3, Seq[T]]]]): Int = map.values.map(total2).sum

  def emit2(
            modelProgram: Program,
            canaryTypes: Seq[TypeTree],
            ecs2: ECS2,
            fcs2: FCS2,
            ls2: LS2
          ): UnitDef = {

    val implicits = (
      for ((tt, ttS2) <- ecs2.toSeq.sortBy { case (tt, ttS2) => (-total3(ttS2), tt.toString) } )
      yield {
        val ttImplicits =
          (for ((idxPar, _) <- ttS2.toSeq.sortBy { case (idxPar, ttParStats) => (-total2(ttParStats), idxPar.toString) })
            yield {
              val labelName: String = idxPar match {
                case Some((idx, par)) =>
                  val parName = par.toString.stripPrefix("class leon.purescala.Expressions$")
                  s"${PCFGEmitter.typeTreeName(tt)}_${idx}_$parName"
                case None => s"${PCFGEmitter.typeTreeName(tt)}_TOPLEVEL"
              }
              val labelId: Identifier = FreshIdentifier(labelName)
              val cd: CaseClassDef = new CaseClassDef(labelId, getTypeParams(tt).map(TypeParameterDef), None, false)
              cd.setFields(Seq(ValDef(FreshIdentifier("v", tt))))

              // cd.addFlag(IsImplicit)
              cd.addFlag(Annotation("label", Seq()))

              idxPar -> cd
            }
          ).toMap
        tt -> ttImplicits
      }
    ).toMap

    val pr1 = for {
      (tt, ttS2) <- ecs2.toSeq.sortBy { case (tt, ttS2) => (-total3(ttS2), tt.toString) }
      (idxPar, ttParS2) <- ttS2.toSeq.sortBy { case (idxPar, ttParS2) => (-total2(ttParS2), idxPar.toString) }
      (constr, ttConstrMap) <- ttParS2.toList.sortBy { case (constr, ttConstrMap) => (-total1(ttConstrMap), constr.toString) }
      if constr != classOf[FunctionInvocation]
      (argTypes, exprs) <- ttConstrMap if exprs.nonEmpty
      production <- emit2Single(
                           modelProgram,
                           tt,
                           idxPar,
                           constr,
                           argTypes,
                           exprs,
                           ecs2,
                           ls2,
                           implicits
                         )
    } yield production

    val pr2 = for {
      (tt, ttS2) <- fcs2.toSeq.sortBy { case (tt, ttS2) => (-total2(ttS2), tt.toString) }
      (idxPar, ttParS2) <- ttS2.toSeq.sortBy { case (idxPar, ttParS2) => (-total1(ttParS2), idxPar.toString) }
      (pos, fis) <- ttParS2.toSeq.sortBy { case (pos, fis) => (-fis.size, pos.toString) }
      prodRule <- emitFunctionCalls2(tt, idxPar, pos, fis, implicits)
    } yield prodRule

    val pr3 = for {
      tt <- canaryTypes
      prodRule <- emitStartProds2(tt, implicits)
    } yield prodRule

    val labels = implicits.values.flatMap(_.values).toSeq
    val defns: Seq[Definition] = labels ++ pr1 ++ pr2 ++ pr3
    val moduleDef = ModuleDef(FreshIdentifier("grammar"), defns, isPackageObject = false)
    val packageRef = List("leon", "grammar")
    new UnitDef(FreshIdentifier("grammar"), packageRef, PCFGEmitter.imports, Seq(moduleDef), isMainUnit = true)

  }

  def emit2Single(
             modelProgram: Program,
             tt: TypeTree,
             idxPar: Option[(Int, Class[_ <: Expr])],
             constr: Class[_ <: Expr],
             argTypes: Seq[TypeTree],
             exprs: Seq[Expr],
             ecs2: ECS2,
             ls2: LS2,
             implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
           ): Seq[FunDef] = {

    if (exprs.head.isInstanceOf[Literal[_]])
      emitLiterals2(tt, idxPar, constr, ls2, implicits)
    else if (constr == classOf[CaseClass])
      emitCaseClass2(tt, idxPar, constr, argTypes, exprs, implicits)
    else
      emitGeneral2(modelProgram, tt, idxPar, constr, argTypes, exprs, implicits)
  }

  def ccCnt = new leon.utils.UniqueCounter[Unit]

  def emitCaseClass2(
    tt: TypeTree,
    idxPar: Option[(Int, Class[_ <: Expr])],
    constr: Class[_ <: Expr],
    argTypes: Seq[TypeTree],
    exprs: Seq[Expr],
    implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
  ): Seq[FunDef] = {
    val classCount = exprs.map(_.asInstanceOf[CaseClass]).groupBy(e => normalizeType(e.ct, false).asInstanceOf[CaseClassType]).mapValues(_.size).toSeq
    classCount map { case (cct, num) =>
      val ccd = cct.classDef
      val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}${ccd.id.name.toString}${ccCnt.nextGlobal}"
      val outputLabel = CaseClassType(implicits(tt)(idxPar), getTypeParams(tt))
      val id: Identifier = FreshIdentifier(productionName, outputLabel, true)

      val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
      val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) =>
        val inputLabel = CaseClassType(implicits(ptt)(Some(idx, constr)), getTypeParams(ptt))
        ValDef(FreshIdentifier(s"v$idx", inputLabel))
      }

      val operands = params.map { p =>
        val labeledT = p.getType.asInstanceOf[CaseClassType]
        CaseClassSelector(labeledT, p.toVariable, labeledT.classDef.fieldsIds.head)
      }

      val fullBody = CaseClass(CaseClassType(ccd, tt.asInstanceOf[ClassType].tps), operands)

      val production: FunDef = new FunDef(id, tparams, params, outputLabel)
      production.fullBody = fullBody

      val frequency: Int = num
      production.addFlag(Annotation("production", Seq(Some(frequency))))

      production

    }


  }

  def emitGeneral2(
                    modelProgram: Program,
                    tt: TypeTree,
                    idxPar: Option[(Int, Class[_ <: Expr])],
                    constr: Class[_ <: Expr],
                    argTypes: Seq[TypeTree],
                    exprs: Seq[Expr],
                    implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                  ): Seq[FunDef] = {

    if (!implicits.contains(tt) || !implicits(tt).contains(idxPar)) {
      println(s"Suppressing production rule for type $tt, $idxPar, $constr, $argTypes: Non-terminal symbol not found")
      // println(s"Head expression: ${exprs.head}")
      return Seq()
    } else {
      argTypes.zipWithIndex.collectFirst {
        case (ptt, idx) if !implicits.contains(ptt) || !implicits(ptt).contains(Some(idx, constr)) =>
          println(s"Suppressing production rule for type $tt, $idxPar, $constr, $argTypes: Mysterious argument $ptt, $idx")
          return Seq()
      }
    }

    val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
    val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}$constrName"
    val outputLabel = CaseClassType(implicits(tt)(idxPar), getTypeParams(tt))
    val id: Identifier = FreshIdentifier(productionName, outputLabel, true)

    val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
    val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) =>
      val inputLabel = CaseClassType(implicits(ptt)(Some(idx, constr)), getTypeParams(ptt))
      ValDef(FreshIdentifier(s"v$idx", inputLabel))
    }

    val operands = params.map { p =>
      val labeledT = p.getType.asInstanceOf[CaseClassType]
      CaseClassSelector(labeledT, p.toVariable, labeledT.classDef.fieldsIds.head)
    }

    val modelExpr = exprs.head
    val typeN = TO.instantiation_<:(modelExpr.getType, tt).get
    val modelExprInst = TO.instantiateType(modelExpr, typeN, Map())
    val Operator(_, op) = modelExprInst
    val fullBody: Expr = {
      if (constr == classOf[Variable]) {
        val fd = modelProgram.library.variable.get
        FunctionInvocation(TypedFunDef(fd, Seq(tt)), Seq())
      } else {
        op(operands)
      }
    }

    val production: FunDef = new FunDef(id, tparams, params, outputLabel)
    production.fullBody = fullBody

    val frequency: Int = exprs.size // TODO! Fix this!
    production.addFlag(Annotation("production", Seq(Some(frequency))))

    Seq(production)

  }

  def emitLiterals2(
                     tt: TypeTree,
                     idxPar: Option[(Int, Class[_ <: Expr])],
                     constr: Class[_ <: Expr],
                     ls2: LS2,
                     implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                   ): Seq[FunDef] = {
    for ((_, literals) <- ls2(tt)(idxPar).toSeq.sortBy(-_._2.size)) yield {
      val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
      val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}$constrName"
      val outputLabel = CaseClassType(implicits(tt)(idxPar), getTypeParams(tt))
      val id: Identifier = FreshIdentifier(productionName, outputLabel, true)

      val tparams: Seq[TypeParameterDef] = Seq()
      val params: Seq[ValDef] = Seq()
      val fullBody: Expr = literals.head

      val production: FunDef = new FunDef(id, tparams, params, outputLabel)
      production.fullBody = fullBody

      val frequency: Int = literals.size // TODO! Fix this!
      production.addFlag(Annotation("production", Seq(Some(frequency))))

      production
    }
  }

  def emitFunctionCalls2(
                         tt: TypeTree,
                         idxPar: Option[(Int, Class[_ <: Expr])],
                         pos: Position,
                         fis: Seq[FunctionInvocation],
                         implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                       ): Seq[FunDef] = {
    if (Stats2Main.REPAIR){
      if (pos.file.toString.contains("library/leon")) return Seq()
    } else {
      if (!PCFGEmitter.libFiles.exists(pos.file.toString.contains)) return Seq() // Ignore non-lib calls
    }
    val tfd = fis.head.tfd

    if (PCFGEmitter.exclude(tfd.fd)) return Seq() // exclude some functions

    val tmap = TO.instantiation_<:(tfd.returnType, tt).get
    val argTypes = tfd.params.map(_.getType).map(TO.instantiateType(_, tmap))
    val labeledArgTypes = argTypes.zipWithIndex.map { case (tp, ind) =>
      CaseClassType(
        implicits(normalizeType(tp)).getOrElse(
          Some((ind, classOf[FunctionInvocation])),
          {
            println(s"Did not find ${normalizeType(tp)} -> ($ind, FunctionInvocation)")
            return Seq()
          }
        ),
        getTypeParams(tp)
      )
    }
    val retType = tt
    val labeledRetType = CaseClassType(
      implicits(normalizeType(tt))(idxPar),
      getTypeParams(tt)
    )
    val params = labeledArgTypes.zipWithIndex.map { case (tp, ind) => ValDef(FreshIdentifier(s"v$ind", tp)) }

    val tparams = getTypeParams(FunctionType(argTypes, retType)).map(TypeParameterDef)

    val id = FreshIdentifier("fd", labeledRetType, true)

    val fd = new FunDef(id, tparams, params, labeledRetType)

    val invocationTps = tfd.tps.map(TO.instantiateType(_, tmap))

    val fullBody = FunctionInvocation(
      tfd.fd.typed(invocationTps),
      params map (p => caseClassSelector(p.toVariable, 0))
    )

    fd.fullBody = fullBody
    fd.addFlag(Annotation("production", Seq(Some(fis.size))))
    Seq(fd)
  }

  def emitStartProds2(
                       tt: TypeTree,
                       implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                     ): Seq[FunDef] ={
    if (!implicits.contains(tt) || !implicits(tt).contains(None)) {
      println(s"Suppressing starting rule for type $tt: Non-terminal symbol not found")
      if (implicits.contains(tt)) {
        println(implicits(tt).keys)
      }
      return Seq()
    }

    val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}Start"
    val outputLabel = tt
    val id = FreshIdentifier(productionName, tt, true)

    val tparams: Seq[TypeParameterDef] = getTypeParams(tt).map(TypeParameterDef)
    val param: ValDef = {
      val inputLabel = CaseClassType(implicits(tt)(None), getTypeParams(tt))
      ValDef(FreshIdentifier(s"v0", inputLabel))
    }
    val fullBody = {
      val labeledT = param.getType.asInstanceOf[CaseClassType]
      CaseClassSelector(labeledT, param.toVariable, labeledT.classDef.fieldsIds.head)
    }

    val production: FunDef = new FunDef(id, tparams, Seq(param), outputLabel)
    production.fullBody = fullBody

    val frequency: Int = 1
    production.addFlag(Annotation("production", Seq(Some(frequency))))

    Seq(production)
  }

}
