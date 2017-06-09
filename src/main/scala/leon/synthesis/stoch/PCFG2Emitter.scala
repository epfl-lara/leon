package leon.synthesis.stoch

import leon.purescala.Common.{FreshIdentifier, Id2, Identifier}
import leon.purescala.Definitions._
import leon.purescala.Expressions.{And, Assert, Choose, Ensuring, Error, Expr, Forall, FunctionInvocation, Let, Literal, NoTree, Or, Passes, Require, Variable}
import leon.purescala.Extractors.Operator
import leon.purescala.Types.{CaseClassType, FunctionType, TypeTree}
import leon.synthesis.stoch.Stats._
import leon.synthesis.stoch.StatsUtils.getTypeParams
import leon.utils.Position

object PCFG2Emitter {

  def total1[K1, T](map: Map[K1, Seq[T]]): Int = map.values.flatten.size
  def total2[K1, K2, T](map: Map[K1, Map[K2, Seq[T]]]): Int = map.values.map(total1).sum
  def total3[K1, K2, K3, T](map: Map[K1, Map[K2, Map[K3, Seq[T]]]]): Int = map.values.map(total2).sum

  def emit2(
            modelProgram: Program,
            canaryTypes: Seq[TypeTree],
            ecs1: ExprConstrStats,
            fcs1: FunctionCallStats,
            ls1: LitStats,
            ecs2: ECS2,
            fcs2: FCS2,
            ls2: LS2
          ): UnitDef = {

    val implicits =
      (for ((tt, ttS2) <- ecs2.toSeq.sortBy { case (tt, ttS2) => (-total3(ttS2), tt.toString) } )
       yield {
         val ttImplicits =
           (for ((idxPar, _) <- ttS2.toSeq.sortBy { case (idxPar, ttParStats) => (-total2(ttParStats), idxPar.toString) })
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
            }).toMap
         tt -> ttImplicits
       }).toMap

    val pr1 = for {
      (tt, ttS2) <- ecs2.toSeq.sortBy { case (tt, ttS2) => (-total3(ttS2), tt.toString) }
      (idxPar, ttParS2) <- ttS2.toSeq.sortBy { case (idxPar, ttParS2) => (-total2(ttParS2), idxPar.toString) }
      (constr, ttConstrMap) <- ttParS2.toList.sortBy { case (constr, ttConstrMap) => (-total1(ttConstrMap), constr.toString) }
      if constr != classOf[FunctionInvocation]
      (argTypes, exprs) <- ttConstrMap if exprs.nonEmpty
      production <- emit2(
                           modelProgram,
                           tt,
                           idxPar,
                           constr,
                           argTypes,
                           exprs,
                           ecs1,
                           fcs1,
                           ls1,
                           ecs2,
                           fcs2,
                           ls2,
                           implicits
                         )
    } yield production

    val pr2 = for {
      (tt, ttS2) <- fcs2.toSeq.sortBy { case (tt, ttS2) => (-total2(ttS2), tt.toString) }
      (idxPar, ttParS2) <- ttS2.toSeq.sortBy { case (idxPar, ttParS2) => (-total1(ttParS2), idxPar.toString) }
      (pos, fis) <- ttParS2.toSeq.sortBy { case (pos, fis) => (-fis.size, pos.toString) }
      prodRule <- emitFunctionCalls2(tt, idxPar, pos, fis, ecs1, fcs1, ls1, ecs2, fcs2, ls2, implicits)
    } yield prodRule

    val pr3 = for {
      tt <- canaryTypes
      prodRule <- emitStartProds2(tt, ecs1, fcs1, ls1, ecs2, fcs2, ls2, implicits)
    } yield prodRule

    val labels = implicits.values.flatMap(_.values).toSeq
    val defns: Seq[Definition] = labels ++ pr1 ++ pr2 ++ pr3
    val moduleDef = ModuleDef(FreshIdentifier("grammar"), defns, isPackageObject = false)
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

  def emit2(
             modelProgram: Program,
             tt: TypeTree,
             idxPar: Option[(Int, Class[_ <: Expr])],
             constr: Class[_ <: Expr],
             argTypes: Seq[TypeTree],
             exprs: Seq[Expr],
             ecs1: ExprConstrStats,
             fcs1: FunctionCallStats,
             ls1: LitStats,
             ecs2: ECS2,
             fcs2: FCS2,
             ls2: LS2,
             implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
           ): Seq[FunDef] = {

    val suppressedConstrs: Set[Class[_ <: Expr]] = Set(classOf[Ensuring], classOf[Require], classOf[Let],
      classOf[Error], classOf[NoTree], classOf[Assert], classOf[Forall], classOf[Passes], classOf[Choose])

    if (suppressedConstrs.contains(constr)) Seq()
    else if ((constr == classOf[And] || constr == classOf[Or]) && argTypes.length != 2) Seq()
    else if ((constr == classOf[And] || constr == classOf[Or]) && argTypes.length == 2) {
      val exprsPrime = ecs2(tt)(idxPar)(constr).values.flatten.toSeq
      emitGeneral2(modelProgram, tt, idxPar, constr, argTypes, exprsPrime, ecs1, fcs1, ls1, ecs2, fcs2, ls2, implicits)
    }
    else if (exprs.head.isInstanceOf[Literal[_]]) {
      emitLiterals2(tt, idxPar, constr, argTypes, exprs, ecs1, fcs1, ls1, ecs2, fcs2, ls2, implicits)
    }
    else emitGeneral2(modelProgram, tt, idxPar, constr, argTypes, exprs, ecs1, fcs1, ls1, ecs2, fcs2, ls2, implicits)

  }

  def emitGeneral2(
                    modelProgram: Program,
                    tt: TypeTree,
                    idxPar: Option[(Int, Class[_ <: Expr])],
                    constr: Class[_ <: Expr],
                    argTypes: Seq[TypeTree],
                    exprs: Seq[Expr],
                    ecs1: ExprConstrStats,
                    fcs1: FunctionCallStats,
                    ls1: LitStats,
                    ecs2: ECS2,
                    fcs2: FCS2,
                    ls2: LS2,
                    implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                  ): Seq[FunDef] = {

    if (!implicits.contains(tt) || !implicits(tt).contains(idxPar)) {
      println(s"Suppressing production rule for type $tt, $idxPar, $constr, $argTypes: Non-terminal symbol not found")
      // println(s"Head expression: ${exprs.head}")
      return Seq()
    } else if (argTypes.zipWithIndex.exists { case (ptt, idx) =>
                  !implicits.contains(ptt) || !implicits(ptt).contains(Some(idx, constr))
               } ) {
      val (ptt, idx) = argTypes.zipWithIndex.find { case (ptt2, idx2) =>
        !implicits.contains(ptt2) || !implicits(ptt2).contains(Some(idx2, constr))
      }.get
      println(s"Suppressing production rule for type $tt, $idxPar, $constr, $argTypes: Mysterious argument $ptt, $idx")
      // println(s"Head expression: ${exprs.head}")
      return Seq()
    }

    val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
    val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}$constrName"
    val outputLabel = CaseClassType(implicits(tt)(idxPar), getTypeParams(tt))
    val id: Identifier = FreshIdentifier(productionName, outputLabel)

    val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
    val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) =>
      val inputLabel = CaseClassType(implicits(ptt)(Some(idx, constr)), getTypeParams(ptt))
      ValDef(FreshIdentifier(s"v$idx", inputLabel))
    }
    val rawParams: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) =>
      val pid = params(idx)
      val id = new Id2(pid, ptt, implicits(ptt)(Some(idx, constr)))
      ValDef(id)
    }
    val Operator(_, op) = exprs.head
    val fullBody: Expr = {
      if (constr == classOf[Variable]) {
        val fd = modelProgram.library.variable.get
        FunctionInvocation(TypedFunDef(fd, Seq(tt)), Seq())
      } else {
        op(rawParams.map(_.toVariable))
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
                     argTypes: Seq[TypeTree],
                     exprs: Seq[Expr],
                     ecs1: ExprConstrStats,
                     fcs1: FunctionCallStats,
                     ls1: LitStats,
                     ecs2: ECS2,
                     fcs2: FCS2,
                     ls2: LS2,
                     implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                   ): Seq[FunDef] = {
    for ((value, literals) <- ls2(tt)(idxPar).toSeq.sortBy(-_._2.size)) yield {
      val constrName: String = constr.toString.stripPrefix("class leon.purescala.Expressions$")
      val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}$constrName"
      val outputLabel = CaseClassType(implicits(tt)(idxPar), getTypeParams(tt))
      val id: Identifier = FreshIdentifier(productionName, outputLabel)

      require(getTypeParams(FunctionType(argTypes, tt)).isEmpty) // Literals cannot be of generic type, can they?
      val tparams: Seq[TypeParameterDef] = Seq()
      require(argTypes.isEmpty) // Literals cannot have arguments, can they?
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
                         ecs1: ExprConstrStats,
                         fcs1: FunctionCallStats,
                         ls1: LitStats,
                         ecs2: ECS2,
                         fcs2: FCS2,
                         ls2: LS2,
                         implicits: Map[TypeTree, Map[Option[(Int, Class[_ <: Expr])], CaseClassDef]]
                       ): Seq[FunDef] = {
    if (pos.file.toString.contains("/leon/library/leon/")) {
      val tfd = fis.head.tfd
      val productionName: String = s"p${PCFGEmitter.typeTreeName(tt)}FunctionInvocation${tfd.id.name}"
      val outputLabel = CaseClassType(implicits(tt)(idxPar), getTypeParams(tt))
      val id: Identifier = FreshIdentifier(productionName, tt)
      val argTypes = tfd.params.map(_.getType)

      if (!implicits.contains(tt) || !implicits(tt).contains(idxPar)) {
        println(s"Suppressing production rule for type $tt, $idxPar, ${tfd.id}: Non-terminal symbol not found")
        // println(s"Head function invocation: ${fis.head}")
        return Seq()
      } else if (argTypes.zipWithIndex.exists { case (ptt, idx) =>
        !implicits.contains(ptt) || !implicits(ptt).contains(Some(idx, classOf[FunctionInvocation]))
      } ) {
        val (ptt, idx) = argTypes.zipWithIndex.find { case (ptt2, idx2) =>
          !implicits.contains(ptt2) || !implicits(ptt2).contains(Some(idx2, classOf[FunctionInvocation]))
        }.get
        println(s"Suppressing production rule for type $tt, $idxPar, ${tfd.id}: Mysterious argument $ptt, $idx")
        // println(s"Head function invocation: ${fis.head}")
        return Seq()
      }

      val tparams: Seq[TypeParameterDef] = getTypeParams(FunctionType(argTypes, tt)).map(TypeParameterDef)
      val params: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) =>
        val inputLabel = CaseClassType(implicits(ptt)(Some(idx, classOf[FunctionInvocation])), getTypeParams(ptt))
        ValDef(FreshIdentifier(s"v$idx", inputLabel))
      }
      val rawParams: Seq[ValDef] = argTypes.zipWithIndex.map { case (ptt, idx) =>
        val pid = params(idx)
        val id = new Id2(pid, ptt, implicits(ptt)(Some(idx, classOf[FunctionInvocation])))
        ValDef(id)
      }
      val fullBody: Expr = FunctionInvocation(tfd, rawParams.map(_.toVariable))

      val production: FunDef = new FunDef(id, tparams, params, outputLabel)
      production.fullBody = fullBody

      val frequency: Int = fis.size // TODO! Fix this!
      production.addFlag(Annotation("production", Seq(Some(frequency))))

      Seq(production)
    } else {
      // Ignore calls to non-library functions
      Seq()
    }
  }

  def emitStartProds2(
                       tt: TypeTree,
                       ecs1: ExprConstrStats,
                       fcs1: FunctionCallStats,
                       ls1: LitStats,
                       ecs2: ECS2,
                       fcs2: FCS2,
                       ls2: LS2,
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
    val id = FreshIdentifier(productionName, tt)

    val tparams: Seq[TypeParameterDef] = getTypeParams(tt).map(TypeParameterDef)
    val params: Seq[ValDef] = Seq {
      val inputLabel = CaseClassType(implicits(tt)(None), getTypeParams(tt))
      ValDef(FreshIdentifier(s"v0", inputLabel))
    }
    val rawParams: Seq[ValDef] = params.map { pid =>
      val id = new Id2(pid, tt, implicits(tt)(None))
      ValDef(id)
    }
    val fullBody: Expr = rawParams.head.toVariable

    val production: FunDef = new FunDef(id, tparams, params, outputLabel)
    production.fullBody = fullBody

    val frequency: Int = 1
    production.addFlag(Annotation("production", Seq(Some(frequency))))

    Seq(production)
  }

}
