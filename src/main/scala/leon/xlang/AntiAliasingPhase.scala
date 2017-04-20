/* Copyright 2009-2015 EPFL, Lausanne */
package leon.xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.DefOps._
import leon.purescala.Types._
import leon.purescala.Constructors._
import leon.purescala.Extractors._
import leon.purescala.DependencyFinder
import leon.purescala.DefinitionTransformer
import leon.utils.Bijection
import leon.xlang.Expressions._
import leon.xlang.ExprOps._

object AntiAliasingPhase extends TransformationPhase {

  val name = "Anti-Aliasing"
  val description = "Make aliasing explicit"


  override def apply(ctx: LeonContext, program: Program): Program = {

    val effectsAnalysis = new EffectsAnalysis

    val transformer = new DefinitionTransformer {
      override def transformType(tpe: TypeTree): Option[TypeTree] = tpe match {
        case (ft: FunctionType) => Some(makeFunctionTypeExplicit(ft, effectsAnalysis))
        case _ => None
      }
    }
    val cdsMap = program.definedClasses.map(cd => cd -> transformer.transform(cd)).toMap
    val fdsMap = program.definedFunctions.map(fd => fd -> transformer.transform(fd)).toMap
    val pgm = replaceDefsInProgram(program)(fdsMap, cdsMap)
    //println(leon.purescala.ScalaPrinter(pgm, ctx))

    val fds = allFunDefs(pgm)

    var updatedFunctions: Map[FunDef, FunDef] = Map()

    //for each fun def, all the vars the the body captures. Only
    //mutable types.
    val varsInScope: Map[FunDef, Set[Identifier]] = (for {
      fd <- fds
    } yield {
      val allFreeVars = fd.body.map(bd => variablesOf(bd)).getOrElse(Set())
      val freeVars = allFreeVars -- fd.params.map(_.id)
      val mutableFreeVars = freeVars.filter(id => effectsAnalysis.isMutableType(id.getType))
      (fd, mutableFreeVars)
    }).toMap

    /*
     * The first pass will introduce all new function definitions,
     * so that in the next pass we can update function invocations
     */
    for {
      fd <- fds
    } {
      updatedFunctions += (fd -> updateFunDef(fd, effectsAnalysis)(ctx))
    }
    //println(updatedFunctions.filter(p => p._1.id != p._2.id).mkString("\n"))

    for {
      fd <- fds
    } {
      updateBody(fd, effectsAnalysis, updatedFunctions, varsInScope)(ctx)
    }

    replaceDefsInProgram(pgm)(updatedFunctions, Map[ClassDef, ClassDef]())

    //pgm.copy(units = for (u <- pgm.units) yield {
    //  u.copy(defs = u.defs.map {
    //    case m : ModuleDef =>
    //      m.copy(defs = for (df <- m.defs) yield {
    //        df match {
    //          case cd : CaseClassDef => ccdBijection.getBorElse(cd, cd)
    //          case fd : FunDef => updatedFunctions.getOrElse(fd, fd)
    //          case d => d
    //        }
    //    })
    //    case cd: CaseClassDef => ccdBijection.getBorElse(cd, cd)
    //    case d => d
    //  })
    //})
  }

  /*
   * Create a new FunDef for a given FunDef in the program.
   * Adapt the signature to express its effects. In case the
   * function has no effect, this will still return the original
   * fundef.
   *
   * Also update FunctionType parameters that need to become explicit
   * about the effect they could perform (returning any mutable type that
   * they receive).
   */
  private def updateFunDef(fd: FunDef, effects: EffectsAnalysis)(ctx: LeonContext): FunDef = {

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    //val newParams = fd.params.map(vd => vd.getType match {
    //  case (ft: FunctionType) => {
    //    val nft = makeFunctionTypeExplicit(ft)
    //    if(ft == nft) vd else ValDef(vd.id.duplicate(tpe = nft))
    //  }
    //  case (cct: CaseClassType) => ccdMap.get(cct.classDef) match {
    //    case Some(ncd) => ValDef(vd.id.duplicate(tpe = ncd.typed))
    //    case None => vd
    //  }
    //  case _ => vd
    //})

    //check is done in EffectsChecking now
    //fd.body.foreach(body => getReturnedExpr(body).flatMap(e => findReferencedIds(e)).foreach((id: Identifier) => {
    //  println("returning: " + id)
    //  if(aliasedParams.contains(id))
    //    ctx.reporter.fatalError(id.getPos, "Cannot return a shared reference to a mutable object")
    //}))

    if(aliasedParams.isEmpty) fd else {
      val newReturnType: TypeTree = tupleTypeWrap(fd.returnType +: aliasedParams.map(_.getType))
      val newFunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, newReturnType)
      newFunDef.addFlags(fd.flags)
      newFunDef.setPos(fd)
      newFunDef
    }
  }

  //private def updateCaseClassDef(ccd: CaseClassDef): CaseClassDef = {
  //  val newFields = ccd.fields.map(vd => vd.getType match {
  //    case (ft: FunctionType) => {
  //      val nft = makeFunctionTypeExplicit(ft)
  //      if(nft == ft) vd else {
  //        ValDef(vd.id.duplicate(tpe = nft))
  //      }
  //    }
  //    case _ => vd
  //  })
  //  if(newFields != ccd.fields) {
  //    ccd.duplicate(fields = newFields)
  //  } else {
  //    ccd
  //  }
  //}

  //recursively update until fixpoint reach
  //private def updateCaseClassDefs(ccdMap: Map[CaseClassDef, CaseClassDef], deps: DependencyFinder, pgm: Program): Map[CaseClassDef, CaseClassDef] = {
  //  for {
  //    ccd <- pgm.singleCaseClasses
  //  } {
  //    if(deps(ccd).exists(_ ==
  //    (ccd, updateCaseClassDef(ccd))).toMap.filter(p => p._1 != p._2) 
  //  }
  //  for
  //}

  private def updateBody(fd: FunDef, effects: EffectsAnalysis, updatedFunDefs: Map[FunDef, FunDef], 
                         varsInScope: Map[FunDef, Set[Identifier]])
                        (ctx: LeonContext): Unit = {

    val ownEffects = effects(fd)
    val aliasedParams: Seq[Identifier] = fd.params.zipWithIndex.flatMap{
      case (vd, i) if ownEffects.contains(i) => Some(vd)
      case _ => None
    }.map(_.id)

    val newFunDef = updatedFunDefs(fd)

    if(aliasedParams.isEmpty) {
      val newBody = fd.body.map(body => {
        makeSideEffectsExplicit(body, fd, Seq(), effects, updatedFunDefs, varsInScope)(ctx)
      })
      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = fd.postcondition
    } else {
      val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
      val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap

      val newBody = fd.body.map(body => {

        val freshBody = rewriteIDs(rewritingMap, body)
        val explicitBody = makeSideEffectsExplicit(freshBody, fd, freshLocalVars, effects, updatedFunDefs, varsInScope)(ctx)

        //only now we rewrite function parameters that changed names when the new function was introduced
        val paramRewritings: Map[Identifier, Identifier] =
          fd.params.zip(newFunDef.params).filter({
            case (ValDef(oid), ValDef(nid)) if oid != nid => true
            case _ => false
          }).map(p => (p._1.id, p._2.id)).toMap
        val explicitBody2 = replaceFromIDs(paramRewritings.map(p => (p._1, p._2.toVariable)), explicitBody)
              

        //WARNING: only works if side effects in Tuples are extracted from left to right,
        //         in the ImperativeTransformation phase.
        val finalBody: Expr = Tuple(explicitBody2 +: freshLocalVars.map(_.toVariable))

        freshLocalVars.zip(aliasedParams).foldLeft(finalBody)((bd, vp) => {
          LetVar(vp._1, Variable(vp._2), bd)
        })

      })

      val newPostcondition = fd.postcondition.map(post => {
        val Lambda(Seq(res), postBody) = post
        val newRes = ValDef(FreshIdentifier(res.id.name, newFunDef.returnType))
        val newBody =
          replace(
            aliasedParams.zipWithIndex.map{ case (id, i) => 
              (id.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap ++
            aliasedParams.map(id =>
              (Old(id), id.toVariable): (Expr, Expr)).toMap +
            (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
          postBody)
        Lambda(Seq(newRes), newBody).setPos(post)
      })

      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = newPostcondition
    }
  }

  //We turn all local val of mutable objects into vars and explicit side effects
  //using assignments. We also make sure that no aliasing is being done.
  private def makeSideEffectsExplicit
                (body: Expr, originalFd: FunDef, aliasedParams: Seq[Identifier], effects: EffectsAnalysis, 
                 updatedFunDefs: Map[FunDef, FunDef], varsInScope: Map[FunDef, Set[Identifier]])
                (ctx: LeonContext): Expr = {

    val newFunDef = updatedFunDefs(originalFd)
                  
    def mapApplication(args: Seq[Expr], nfi: Expr, nfiType: TypeTree, fiEffects: Set[Int], rewritings: Map[Identifier, Expr]): Expr = {
      if(fiEffects.nonEmpty) {
        val modifiedArgs: Seq[(Seq[Identifier], Expr)] =
          args.zipWithIndex.filter{ case (arg, i) => fiEffects.contains(i) }
              .map(arg => {
                    val rArg = replaceFromIDs(rewritings, arg._1)
                    (findReferencedIds(rArg).filter(id => effects.isMutableType(id.getType)), rArg)
                   })

        {//testing if duplicated mutable params are sent to a function
          val allParams: Seq[Identifier] =
            args.zipWithIndex.filter(p => effects.isMutableType(p._1.getType)).map(arg => {
                      val rArg = replaceFromIDs(rewritings, arg._1)
                      (findReferencedIds(rArg).filter(id => effects.isMutableType(id.getType)), rArg)
                     })
                .flatMap(_._1)
          val duplicatedParams = allParams.diff(allParams.distinct).distinct
          if(duplicatedParams.nonEmpty) 
            ctx.reporter.fatalError(nfi.getPos, "Illegal passing of aliased parameter: " + duplicatedParams.head)
          //TODO: The case f(A(x1,x1,x1)) could probably be handled by forbidding creation at any program point of
          //      case class with multiple refs as it is probably not useful
        }

        val freshRes = FreshIdentifier("res", nfiType)

        val extractResults = Block(
          modifiedArgs.zipWithIndex.flatMap{ case ((idsForIndex, expr), index) => idsForIndex.map(id => {
            val resSelect = TupleSelect(freshRes.toVariable, index + 2)
            expr match {
              case cs@CaseClassSelector(_, obj, mid) =>
                val (rec, path) = fieldPath(cs)
                Assignment(id, objectUpdateToCopy(rec, path, resSelect)).setPos(cs)
              case as@ArraySelect(array, index) =>
                val (rec, path) = fieldPath(as)
                Assignment(id, objectUpdateToCopy(rec, path, resSelect)).setPos(as)
              case cc@CaseClass(cct, es) =>
                val ccd = cct.classDef
                val (_, vd) = es.zip(ccd.fields).find{
                  case (Variable(argId), _) => argId == id
                  case _ => false
                }.get
                Assignment(id, CaseClassSelector(cct, resSelect, vd.id))
                //TODO: this only checks for a top level modified id,
                //      must generalize to any number of nested case classes
                //      must also handle combination of case class and selectors
                
              case _ =>
                Assignment(id, resSelect).setPos(expr)
            }
          })},
          TupleSelect(freshRes.toVariable, 1))


        val newExpr = Let(freshRes, nfi, extractResults)
        newExpr
      } else {
        nfi
      }
    }

    //println("aliased params: " + aliasedParams)
    preMapWithContext[(Set[Identifier], Map[Identifier, Expr], Set[Expr], Boolean)]((expr, context) => {
      val bindings = context._1
      val rewritings = context._2
      val toIgnore = context._3
      val insideEnsuring = context._4
      expr match {

        case l@Let(id, v, b) if effects.isMutableType(id.getType) => {
          val varDecl = LetVar(id, v, b).setPos(l)
          (Some(varDecl), (bindings + id, rewritings, toIgnore, insideEnsuring))
        }

        //case l@Let(id, IsTyped(v, CaseClassType(ccd, _)), b) if ccdMap.contains(ccd) => {
        //  val ncd = ccdMap(ccd)
        //  val freshId = id.duplicate(tpe = ncd.typed)
        //  val freshBody = replaceFromIDs(Map(id -> freshId.toVariable), b)
        //  (Some(Let(freshId, v, freshBody).copiedFrom(l)), context)
        //}

        case l@LetVar(id, IsTyped(v, tpe), b) if effects.isMutableType(tpe) => {
          (None, (bindings + id, rewritings, toIgnore, insideEnsuring))
        }

        case m @ MatchExpr(scrut @ ArraySelect(array, index), cases) if effects.isMutableType(scrut.getType) && !index.isInstanceOf[Variable] => {
          // Bind the index to a new value when it's not already a variable.
          // The effect of this is to prevent recomputation of the index in the cases.
          // The actual work is defered to the next `case`
          val indexId = FreshIdentifier("index", index.getType)
          val newTree = Let(indexId, index, MatchExpr(ArraySelect(array, indexId.toVariable), cases))
          (Some(newTree), context)
        }

        case m@MatchExpr(scrut, cses) if effects.isMutableType(scrut.getType) => {
          val tmp: Map[Identifier, Expr] = cses.flatMap{ case MatchCase(pattern, guard, rhs) => {
            mapForPattern(scrut, pattern)
            //val binder = pattern.binder.get
            //binder -> scrut
          }}.toMap

          (None, (bindings, rewritings ++ tmp, toIgnore, insideEnsuring))
        }

        case up@ArrayUpdate(a, i, v) => {
          val ra = replaceFromIDs(rewritings, a)

          val (receiver, path) = fieldPath(ra, List(ArrayIndex(i)))

          findReceiverId(receiver) match {
            case Some(id) =>
              if(bindings.contains(id)) {
                val assign = Assignment(id, objectUpdateToCopy(receiver, path, v).setPos(up)).setPos(up)
                (Some(assign), context)
              } else (None, context)
            case None =>
              ctx.reporter.fatalError(up.getPos, "Unsupported form of array update: " + up)
          }

          //  case CaseClassSelector(_, o, id) => //should be a path in an object, with id the array to update in the object
          //    findReceiverId(o) match {
          //      case None =>
          //        ctx.reporter.fatalError(up.getPos, "Unsupported form of array update: " + up)
          //      case Some(oid) => {
          //        if(bindings.contains(oid)) {
          //          (Some(Assignment(oid, deepCopy(ArraySelect(ra, i), v).setPos(up))), context)

          //          val (rec, path) = fieldPath(cs)
          //          Assignment(oid, objectUpdateToCopy(rec, path, resSelect))
          //        else
          //          (None, context)
          //      }
          //    }
          //  case _ =>
          //    ctx.reporter.fatalError(up.getPos, "Unsupported form of array update: " + up)
          //}
        }

        case as@FieldAssignment(o, id, v) => {
          val so = replaceFromIDs(rewritings, o)

          val (receiver, path) = fieldPath(so, List(ClassField(id)))
          findReceiverId(so) match {
            case None =>
              ctx.reporter.fatalError(as.getPos, "Unsupported form of field assignment: " + as)
            case Some(oid) => {
              if(bindings.contains(oid)) {
                //(Some(Assignment(oid, deepCopy(CaseClassSelector(o.getType.asInstanceOf[CaseClassType], so, id), v))), context)
                val assign = Assignment(oid, objectUpdateToCopy(receiver, path, v).setPos(as)).setPos(as)
                (Some(assign), context)
              } else
                (None, context)
            }
          }
        }

        //we need to replace local fundef by the new updated fun defs.
        case l@LetDef(fds, body) => {
          //this might be traversed several times in case of doubly nested fundef,
          //so we need to ignore the second times by checking if updatedFunDefs 
          //contains a mapping or not
          val nfds = fds.map(fd => updatedFunDefs.get(fd).getOrElse(fd))
          (Some(LetDef(nfds, body).copiedFrom(l)), context)
        }

        case Ensuring(_, _) => (None, (context._1, context._2, context._3, true))
        case lambda@Lambda(params, body) => {
          val ft@FunctionType(_, _) = lambda.getType
          val ownEffects = effects.functionTypeEffects(ft)
          val aliasedParams: Seq[Identifier] = params.zipWithIndex.flatMap{
            case (vd, i) if ownEffects.contains(i) => Some(vd)
            case _ => None
          }.map(_.id)

          if(insideEnsuring || aliasedParams.isEmpty) {
            (None, context)
          } else {
            val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
            val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap
            val freshBody = replaceFromIDs(rewritingMap.map(p => (p._1, p._2.toVariable)), body) 
            val explicitBody = makeSideEffectsExplicit(freshBody, originalFd, freshLocalVars, effects, updatedFunDefs, varsInScope)(ctx)

            //WARNING: only works if side effects in Tuples are extracted from left to right,
            //         in the ImperativeTransformation phase.
            val finalBody: Expr = Tuple(explicitBody +: freshLocalVars.map(_.toVariable))

            val wrappedBody: Expr = freshLocalVars.zip(aliasedParams).foldLeft(finalBody)((bd, vp) => {
              LetVar(vp._1, Variable(vp._2), bd)
            })
            val finalLambda = Lambda(params, wrappedBody).copiedFrom(lambda)

            (Some(finalLambda), context)
          }

        }

        case fi@FunctionInvocation(fd, args) => {

          val vis: Set[Identifier] = varsInScope.get(fd.fd).getOrElse(Set())
          args.find({
            case Variable(id) => vis.contains(id)
            case _ => false
          }).foreach(aliasedArg =>
            ctx.reporter.fatalError(aliasedArg.getPos, "Illegal passing of aliased parameter: " + aliasedArg))



          updatedFunDefs.get(fd.fd) match {
            case None => (None, context)
            case Some(nfd) => {
              val nfi = FunctionInvocation(nfd.typed(fd.tps), args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(fi)
              val fiEffects = effects(fd.fd)
              (Some(mapApplication(args, nfi, nfd.typed(fd.tps).returnType, fiEffects, rewritings)), context)
            }
          }
        }

        case app@Application(callee, args) => {
          if(toIgnore(app)) (None, context) else {
            val ft@FunctionType(_, to) = callee.getType
            to match {
              case TupleType(tps) if effects.isMutableType(tps.last) => {
                val nfi = Application(callee, args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(app)
                val fiEffects = effects.functionTypeEffects(ft)
                (Some(mapApplication(args, nfi, to, fiEffects, rewritings)), (bindings, rewritings, toIgnore + nfi, insideEnsuring))
              }
              case _ => (None, context)
            }
          }
        }

        //case app@Application(callee@Variable(id), args) => {
        //  originalFd.params.zip(newFunDef.params)
        //                   .find(p => p._1.id == id)
        //                   .map(p => p._2.id) match {
        //    case Some(newId) =>
        //      val ft@FunctionType(_, _) = callee.getType
        //      val nft = makeFunctionTypeExplicit(ft)

        //      if(ft == nft) (None, context) else {
        //        val nfi = Application(Variable(newId).copiedFrom(callee), args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(app)
        //        val fiEffects = functionTypeEffects(ft)
        //        (Some(mapApplication(args, nfi, nft.to, fiEffects, rewritings)), context)
        //      }
        //    case None => (None, context)
        //  }
        //}

        //case app@Application(callee@CaseClassSelector(cct, obj, id), args) => {
        //  ccdMap.get(cct.classDef) match {
        //    case None =>
        //      (None, context)
        //    case Some(ncd) => {
        //      val nid = cct.classDef.fields.zip(ncd.fields).find(p => id == p._1.id).map(_._2.id).get
        //      val nccs = CaseClassSelector(ncd.typed, obj, nid).copiedFrom(callee)
        //      val nfi = Application(nccs, args.map(arg => replaceFromIDs(rewritings, arg))).copiedFrom(app)
        //      val ft@FunctionType(_, _) = callee.getType
        //      val nft = makeFunctionTypeExplicit(ft)
        //      val fiEffects = functionTypeEffects(ft)
        //      (Some(mapApplication(args, nfi, nft.to, fiEffects, rewritings)), context)
        //    }
        //  }
        //}

        //case CaseClass(cct, args) => {
        //  ccdMap.get(cct.classDef) match {
        //    case None =>
        //      (None, context)
        //    case Some(ncd) => {
        //      (Some(CaseClass(ncd.typed, args)), context)
        //    }
        //  }
        //}

        case _ => (None, context)
      }

    })(body, (aliasedParams.toSet, Map(), Set(), false))
  }


  //convert a function type with mutable parameters, into a function type
  //that returns the mutable parameters. This makes explicit all possible
  //effects of the function. This should be used for higher order functions
  //declared as parameters.
  private def makeFunctionTypeExplicit(tpe: FunctionType, effects: EffectsAnalysis): FunctionType = {
    val newReturnTypes = tpe.from.filter(t => effects.isMutableType(t))
    if(newReturnTypes.isEmpty)
      tpe
    else {
      FunctionType(tpe.from, TupleType(tpe.to +: newReturnTypes))
    }
  }


  /*
   * A bit hacky, but not sure of the best way to do something like that
   * currently.
   */
  private def getReturnedExpr(expr: Expr): Seq[Expr] = expr match {
    case Let(_, _, rest) => getReturnedExpr(rest)
    case LetVar(_, _, rest) => getReturnedExpr(rest)
    case Block(_, rest) => getReturnedExpr(rest)
    case IfExpr(_, thenn, elze) => getReturnedExpr(thenn) ++ getReturnedExpr(elze)
    case MatchExpr(_, cses) => cses.flatMap{ cse => getReturnedExpr(cse.rhs) }
    case e => Seq(expr)
  }


  /*
   * returns all fun def in the program, including local definitions inside
   * other functions (LetDef).
   */
  private def allFunDefs(pgm: Program): Seq[FunDef] =
      pgm.definedFunctions.flatMap(fd => 
        fd.body.toSet.flatMap((bd: Expr) =>
          nestedFunDefsOf(bd)) + fd)


  //returns a list, to check for duplicates if necessary
  private def findReferencedIds(o: Expr): List[Identifier] = o match {
    case Variable(id) => List(id)
    case CaseClassSelector(_, e, _) => findReferencedIds(e)
    case CaseClass(_, es) => es.foldLeft(List[Identifier]())((acc, e) => acc ::: findReferencedIds(e))
    case AsInstanceOf(e, _) => findReferencedIds(e)
    case ArraySelect(a, _) => findReferencedIds(a)
    case _ => List()
  }
  private def findReceiverId(o: Expr): Option[Identifier] = o match {
    case Variable(id) => Some(id)
    case CaseClassSelector(_, e, _) => findReceiverId(e)
    case AsInstanceOf(e, ct) => findReceiverId(e)
    case ArraySelect(a, _) => findReceiverId(a)
    case _ => None
  }


  //private def extractFieldPath(o: Expr): (Expr, List[Identifier]) = {
  //  def rec(o: Expr): List[Identifier] = o match {
  //    case CaseClassSelector(_, r, i) =>
  //      val res = toFieldPath(r)
  //      (res._1, i::res)
  //    case expr => (expr, Nil)
  //  }
  //  val res = rec(o)
  //  (res._1, res._2.reverse)
  //}

  private sealed trait Field
  private case class ClassField(id: Identifier) extends Field
  private case class ArrayIndex(e: Expr) extends Field

  //given a nested arrayselect and class selectors, return the receiver expression along
  //with the path from left to right
  //Does not consider FieldAssignment and ArrayUpdate as they only make sense on
  //the first level, and it seems cleaner to define path only on select operators
  private def fieldPath(e: Expr, accPath: List[Field] = Nil): (Expr, List[Field]) = e match {
    case CaseClassSelector(_, r, id) => fieldPath(r, ClassField(id) :: accPath)
    case as@ArraySelect(a, index) => fieldPath(a, ArrayIndex(index) :: accPath)
    case e => (e, accPath)
  }


  //given a receiver object (mutable class or array, usually as a reference id),
  //and a path of field/index access, build a copy of the original object, with
  //properly updated values
  private def objectUpdateToCopy(receiver: Expr, path: List[Field], newValue: Expr): Expr = path match {
    case ClassField(id) :: fs =>
      val ct@CaseClassType(ccd, _) = receiver.getType
      val rec = objectUpdateToCopy(CaseClassSelector(CaseClassType(ct.classDef, ct.tps), receiver, id), fs, newValue).setPos(newValue)
      copy(receiver, id, rec)

    case ArrayIndex(index) :: fs =>
      val rec = objectUpdateToCopy(ArraySelect(receiver, index).setPos(newValue), fs, newValue)
      ArrayUpdated(receiver, index, rec).setPos(newValue)

    case Nil => newValue
  }

  //def deepCopy(rec: Expr, nv: Expr): Expr = {
  //  rec match {
  //    case CaseClassSelector(_, r, id) =>
  //      val sub = copy(r, id, nv)
  //      deepCopy(r, sub)
  //    case as@ArraySelect(a, index) =>
  //      deepCopy(a, ArrayUpdated(a, index, nv).setPos(as))
  //    case expr => nv
  //  }
  //}

  private def copy(cc: Expr, id: Identifier, nv: Expr): Expr = {
    val ct@CaseClassType(ccd, _) = cc.getType
    val newFields = ccd.fields.map(vd =>
      if(vd.id == id)
        nv
      else
        CaseClassSelector(CaseClassType(ct.classDef, ct.tps), cc, vd.id).setPos(cc)
    )
    CaseClass(CaseClassType(ct.classDef, ct.tps), newFields).setPos(cc.getPos)
  }

}
