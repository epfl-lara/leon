/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._
import TypeUtil._
import TVarFactory._
import invariant.structure.FunctionUtils._
import laziness._
import InstUtil._
import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

/**
 * An instrumentation phase that performs a sequence of instrumentations
 */
object InstrumentationPhase extends TransformationPhase {
  val name = "Instrumentation Phase"
  val description = "Instruments the program for all counters needed"

  def apply(ctx: LeonContext, program: Program): Program = {
    val instrumenterFactory: SerialInstrumenter => Map[Instrumentation, Instrumenter] =
      si =>
        Map(Time -> new TimeInstrumenter(program, si),
          Depth -> new DepthInstrumenter(program, si),
          Rec -> new RecursionCountInstrumenter(program, si),
          Stack -> new StackSpaceInstrumenter(program, si),
          TPR -> new TPRInstrumenter(program, si),
          Alloc -> new AllocInstrumenter(program, si))
    val si = new SerialInstrumenter(program, instrumenterFactory)
    val instprog = si.apply
    //println("Instrumented Program: "+ScalaPrinter.apply(instprog, purescala.PrinterOptions(printUniqueIds = true)))
    instprog
  }
}

class SerialInstrumenter(program: Program,
                         instFactory: SerialInstrumenter => Map[Instrumentation, Instrumenter],
                         exprInstOpt: Option[InstruContext => ExprInstrumenter] = None) {
  val debugInstrumentation = false

  val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)

  val exprInstFactory = exprInstOpt.getOrElse((ictx: InstruContext) => new ExprInstrumenter(ictx))

  val instToInstrumenter: Map[Instrumentation, Instrumenter] = instFactory(this)

  // a map from functions to the list of instrumentations to be performed for the function
  val (funcInsts, ftypeInsts) = {
    def update[T](fd: T, inst: Instrumentation, emap: MutableMap[T, List[Instrumentation]]) {
      if (emap.contains(fd))
        emap(fd) = (emap(fd) :+ inst).distinct
      else emap.update(fd, List(inst))
    }
    var fdmap = MutableMap[FunDef, List[Instrumentation]]()
    var ftypeMap = MutableMap[CompatibleType, List[Instrumentation]]()
    instToInstrumenter.values.foreach { m =>
      m.functionsToInstrument.foreach {
        case (fd, instsToPerform) =>
          instsToPerform.foreach(instToPerform => update(fd, instToPerform, fdmap))
      }
      m.functionTypesToInstrument.foreach {
        case (ft, instsToPerform) =>
          instsToPerform.foreach(instToPerform => update(ft, instToPerform, ftypeMap))
      }
    }
    (fdmap.toMap, ftypeMap.toMap)
  }
  val instFuncs = funcInsts.keySet
  val instFuncTypes = ftypeInsts.keySet
  //println(s"instfuncs: ${instFuncs.map(_.id).mkString(",")} instFuncTypes: ${instFuncTypes.mkString(",")}")

  val hasMemoFuns = {
    if (instFuncs.exists { fd => fd.hasLazyFieldFlag || HOMemUtil.hasMemAnnotation(fd) }) {
      println("Warning: found Lazy/memoized functions/fields. To verify the program use --mem option")
      true
    } else false
  }
  /**
   * Tracks the instrumentations necessary for a function type
   */
  def instsOfLambdaType(ft: FunctionType): Seq[Instrumentation] = {
    ftypeInsts.getOrElse(new CompatibleType(ft), Seq())
  }

  val adtRootsToInstrument = {
    Util.fix((adts: Set[ClassDef]) => {
      adts ++ program.definedClasses.collect {
        case cd: CaseClassDef if (cd.fields.map(_.getType).exists {
          case ft: FunctionType => instFuncTypes(new CompatibleType(ft))
          case ct: ClassType    => adts(ct.classDef)
          case _                => false
        }) =>
          cd.root
      }.toSet
    })(Set[ClassDef]())
  }

  val adtSpecializer = new ADTSpecializer()
  val adtMap = adtRootsToInstrument.foldLeft(Map[ClassDef, ClassDef]()) {
    case (acc, root) => acc ++ adtSpecializer.copyADTHierarchy(root)
  }
  // set fields of the adt
  adtRootsToInstrument.foreach { oldt => adtSpecializer.specializeFields(oldt, adtMap(oldt), instrumentType) }

  def mapClassType[T <: ClassType](ct: T): T = ct match {
    case CaseClassType(cd, tps) =>
      val ntps = tps map instrumentType
      if (adtMap.contains(cd))
        CaseClassType(adtMap(cd).asInstanceOf[CaseClassDef], ntps).asInstanceOf[T]
      else
        CaseClassType(cd, ntps).asInstanceOf[T]
    case AbstractClassType(ad, tps) =>
      val ntps = tps map instrumentType
      if (adtMap.contains(ad))
        AbstractClassType(adtMap(ad).asInstanceOf[AbstractClassDef], ntps).asInstanceOf[T]
      else
        AbstractClassType(ad, ntps).asInstanceOf[T]
  }

  def instrumentType(t: TypeTree): TypeTree = {
    t match {
      case ft @ FunctionType(argts, rett) =>
        val instTypes = instsOfLambdaType(ft).map(_.getType)
        if (!instTypes.isEmpty)
          FunctionType(argts map instrumentType, TupleType(instrumentType(rett) +: instTypes))
        else ft
      case ct: ClassType => mapClassType(ct)
      case t             => t
    }
  }

  //create new functions. Augment the return type of a function iff the postcondition uses
  //the instrumentation variable or if the function is transitively called from such a function
  val funMap = (userLevelFunctions(program) ++ instFuncs).distinct.map { fd =>
    val newparams = fd.params.map { vd =>
      val rept = instrumentType(vd.getType)
      if (rept == vd.getType) vd
      else ValDef(FreshIdentifier(vd.id.name, rept))
    }
    val nretType = instrumentType(fd.returnType)
    if (instFuncs.contains(fd)) {
      val newRetType = TupleType(nretType +: funcInsts(fd).map(_.getType))
      // let the names of the function encode the kind of instrumentations performed
      val freshId = FreshIdentifier(fd.id.name + "-" + funcInsts(fd).map(_.name).mkString("-"), newRetType)
      (fd -> new FunDef(freshId, fd.tparams, newparams, newRetType))
    } else {
      //here we need not augment the return types but do need to create a new copy
      (fd -> new FunDef(FreshIdentifier(fd.id.name, fd.returnType), fd.tparams, newparams, nretType))
    }
  }.toMap

  //println("Functions with mappings: "+(instFuncs).map(_.id))

  def instrumenters(fd: FunDef) = funcInsts(fd) map instToInstrumenter.apply _

  def instIndex(fd: FunDef)(ins: Instrumentation) = funcInsts(fd).indexOf(ins) + 2

  def instIndex(ft: FunctionType)(ins: Instrumentation) = ftypeInsts(new CompatibleType(ft)).indexOf(ins) + 2

  def selectInst(fd: FunDef)(e: Expr, ins: Instrumentation) = TupleSelect(e, instIndex(fd)(ins))

  def selectInst(ft: FunctionType)(e: Expr, ins: Instrumentation) = TupleSelect(e, instIndex(ft)(ins))

  def mapExpr(ine: Expr, paramMap: Map[Identifier, Identifier]): Expr = {
    def rec(e: Expr)(implicit idMap: Map[Identifier, Identifier]): Expr = e match {
      case _ if instCall(e).isDefined =>
        mapInstCallWithArgs(e, rec)

      case FunctionInvocation(TypedFunDef(fd, targs), args) =>
        val nfd = funMap.getOrElse(fd, fd)
        val ntargs = targs map instrumentType
        val nargs = args map rec
        if (instFuncs.contains(fd))
          TupleSelect(FunctionInvocation(TypedFunDef(nfd, ntargs), nargs), 1)
        else {
          FunctionInvocation(TypedFunDef(nfd, ntargs), nargs)
        }
      case ClassExpr(ct, args, op) =>
        op(mapClassType(ct))(args map rec)
      case app @ Application(l, args) =>
        if (instFuncTypes.contains(new CompatibleType(l.getType))) {
          TupleSelect(Application(rec(l), args map rec), 1)
        } else Application(rec(l), args map rec)
      case Let(id, v, b) =>
        val nv = rec(v)
        if (id.getType != nv.getType) {
          val fid = FreshIdentifier(id.name, nv.getType)
          Let(fid, nv, rec(b)(idMap + (id -> fid)))
        } else
          Let(id, nv, rec(b))
      case MatchExpr(scr, cases) =>
        val nscr = rec(scr)
        val ncases = cases map {
          case MatchCase(pat, optGuard, rhs) =>
            val (npat, newmap) = mapCasePattern(pat, nscr.getType)
            val trans = (e: Expr) => rec(e)(idMap ++ newmap)
            MatchCase(npat, optGuard map trans, trans(rhs))
        }
        MatchExpr(nscr, ncases)
      case Variable(id) => idMap.getOrElse(id, id).toVariable
      case Operator(args, op) =>
        op(args map rec)
    }
    rec(ine)(paramMap)
  }

  def mapCasePattern(ipat: Pattern, scrutType: TypeTree): (Pattern, Map[Identifier, Identifier]) = {
    var idmap = Map[Identifier, Identifier]()
    def makeIdOfType(oldId: Identifier, tpe: TypeTree): Identifier = {
      if (oldId.getType != tpe) {
        val freshid = FreshIdentifier(oldId.name, tpe, true)
        idmap += (oldId -> freshid)
        freshid
      } else oldId
    }
    def mapPattern(p: Pattern, expType: TypeTree): Pattern = {
      p match {
        case InstanceOfPattern(bopt, ict) =>
          val nct = mapClassType(ict)
          val nbopt = bopt.map(makeIdOfType(_, nct))
          InstanceOfPattern(nbopt, nct)
        case CaseClassPattern(bopt, ict, subpats) =>
          val nct = mapClassType(ict)
          val nbopt = bopt.map(makeIdOfType(_, nct))
          val npats = (subpats zip nct.fieldsTypes).map {
            case (p, t) => mapPattern(p, t)
          }
          CaseClassPattern(nbopt, nct, npats)
        case TuplePattern(bopt, subpats) =>
          val TupleType(subts) = expType
          val npats = (subpats zip subts).map {
            case (p, t) => mapPattern(p, t)
          }
          val nbopt = bopt.map(makeIdOfType(_, expType))
          TuplePattern(nbopt, npats)
        case WildcardPattern(bopt) =>
          WildcardPattern(bopt.map(makeIdOfType(_, expType)))
        case lp @ LiteralPattern(bopt, lit) => lp
        case _ =>
          throw new IllegalStateException("Not supported yet!")
      }
    }
    (mapPattern(ipat, scrutType), idmap)
  }

  def mapInstCallWithArgs(e: Expr, mapFun: Expr => Expr) = {
    instCall(e) match {
      case None => throw new IllegalStateException(s"Expr not an inst call" + e)
      case Some(inst) =>
        e match {
          case FunctionInvocation(_, Seq(instArg)) => // here, e has to be of this form
            instArg match {
              case FunctionInvocation(TypedFunDef(fd, targs), args) =>
                val ntargs = targs map instrumentType
                val nargs = args map mapFun
                TupleSelect(FunctionInvocation(TypedFunDef(funMap(fd), ntargs), nargs), instIndex(fd)(inst))

              case Application(fterm, args) =>
                val nargs = (fterm +: args) map mapFun //lambda has to be instrumented here
                val ftype = fterm.getType.asInstanceOf[FunctionType]
                TupleSelect(Application(nargs.head, nargs.tail), instIndex(ftype)(inst))
            }
          case _ => throw new IllegalStateException(s"Cannot use an instrumentation variable in body without arugments" + e)
        }
    }
  }

  def apply: Program = {
    if (instFuncs.isEmpty) program
    else {
      def mapBody(body: Expr, from: FunDef, to: FunDef, paramMap: Map[Identifier, Identifier]) = {
        val res =
          if (from.isExtern) {
            // this is an extern function, we must only rely on the specs
            // so make the body empty
            NoTree(to.returnType)
          } else if (instFuncs.contains(from)) {
            val ictx = new InstruContext(from, this, funcInsts(from))
            exprInstFactory(ictx)(body, paramMap)
          } else {
            mapExpr(body, paramMap)
          }
        res
      }
      def mapPost(pred: Expr, from: FunDef, to: FunDef, paramMap: Map[Identifier, Identifier]) = {
        pred match {
          case Lambda(Seq(ValDef(fromRes)), postCond) if (instFuncs.contains(from)) =>
            val toResId = FreshIdentifier(fromRes.name, to.returnType, true)
            val newpost = postMap((e: Expr) => e match {
              case Variable(`fromRes`) =>
                Some(TupleSelect(toResId.toVariable, 1))
              case _ if instCall(e).isDefined =>
                val inst = instCall(e).get
                inst.instTarget(e) match {
                  case None => // e refers to the resource usage of the current function
                    Some(TupleSelect(toResId.toVariable, instIndex(from)(inst)))
                  case _ => None // this case will be handled by mapExpr
                }
              case _ => None
            })(postCond)
            // here, we can introduce additional properties that must hold
            val instProps = instrumenters(from).flatMap{ m =>
                m.instProp(TupleSelect(toResId.toVariable, instIndex(from)(m.inst)))(from) match {
                  case Some(e) => Seq(e)
                  case None => Seq()
                }
            }
            Lambda(Seq(ValDef(toResId)), createAnd(instProps :+ mapExpr(newpost, paramMap)))
          case _ =>
            mapExpr(pred, paramMap)
        }
      }

      // Map the bodies and preconditions
      for ((from, to) <- funMap) {
        //copy annotations
        from.flags.foreach(to.addFlag(_))
        val paramMap = (from.params.map(_.id) zip to.params.map(_.id)).toMap
        // copy decreases (but it should not use instrumentation)
        if(from.decreaseMeasure.filter(exists(InstUtil.instCall(_).isDefined)).isDefined) {
          throw LeonFatalError("The decreases caluse of function: "+from.id+" uses resource variable!")
        }
        to.decreaseMeasure = from.decreaseMeasure.map(mapExpr(_, paramMap))
        to.fullBody = from.fullBody match {
          case b @ NoTree(_) => NoTree(to.returnType)
          case Require(pre, body) =>
            //here 'from' does not have a postcondition but 'to' will always have a postcondition
            val toPost =
              Lambda(Seq(ValDef(FreshIdentifier("res", to.returnType))), BooleanLiteral(true))
            val bodyPre =
              Require(mapExpr(pre, paramMap), mapBody(body, from, to, paramMap))
            Ensuring(bodyPre, toPost)
          case Ensuring(Require(pre, body), post) =>
            Ensuring(Require(mapExpr(pre, paramMap), mapBody(body, from, to, paramMap)),
              mapPost(post, from, to, paramMap))
          case Ensuring(body, post) =>
            Ensuring(mapBody(body, from, to, paramMap), mapPost(post, from, to, paramMap))
          case body =>
            val toPost =
              Lambda(Seq(ValDef(FreshIdentifier("res", to.returnType))), BooleanLiteral(true))
            Ensuring(mapBody(body, from, to, paramMap), toPost)
        }
      }
      import ExprInstrumenter._
      val additionalFuncs = (funMap.flatMap {
        case (k, _) =>
          if (instFuncs(k))
            instrumenters(k).flatMap(_.additionalfunctionsToAdd)
          else List()
      }.toList.distinct ++
        (if (hasMemoFuns) Seq(lookupFun, updateFun, anyList) else Seq()))
      val mainModule = program.units.find(_.isMainUnit).get.modules.head
      val newprog = copyProgram(program, (defs: Seq[Definition]) =>
        defs.flatMap {
          case fd: FunDef if funMap.contains(fd) =>
            Seq(funMap(fd))
          case cd: ClassDef if adtMap.contains(cd) =>
            Seq(cd, adtMap(cd)) // add both classes
          case d => Seq(d)
        }, Map(mainModule -> additionalFuncs))

      if (debugInstrumentation)
        println("After Instrumentation: \n" + ScalaPrinter.apply(newprog))

      ProgramSimplifier(newprog, instFuncs.toSeq)
    }
  }
}

/**
 * A set of paramteres that need to be passed around
 */
class InstruContext(
    val currFun: FunDef,
    val serialInst: SerialInstrumenter,
    val insts: Seq[Instrumentation],
    val enclLambda: Option[Lambda] = None) {

  val instrumenters = insts map serialInst.instToInstrumenter.apply _
  val instTypes = insts.map(_.getType)
  val funMap = serialInst.funMap
  val adtMap = serialInst.adtMap
  /**
   * Index of the instrumentation 'inst' in result tuple that would be created.
   * The return value will be >= 2 as the actual result value would be at index 1
   */
  def instIndex(ins: Instrumentation) = insts.indexOf(ins) + 2
  def selectInst(e: Expr, ins: Instrumentation) = TupleSelect(e, instIndex(ins))
}

object ExprInstrumenter {
  val instVarContext = newContext
  def createInstVar(name: String, tpe: TypeTree) = createTemp(name, tpe, instVarContext)
  def isInstVar(id: Identifier) = isTemp(id, instVarContext)

  /**
   * The following are stubs for the classes/methods that update and lookup the cache.
   * These methods are defined in the library but are marked "ignore", so we cannot refer to them.
   */
  lazy val anyList = new CaseClassDef(FreshIdentifier("List", Untyped), Seq(), None, false)
  lazy val lookupFun = {
    val tparam = TypeParameter.fresh("T")
    new FunDef(FreshIdentifier("lookup", Untyped), Seq(TypeParameterDef(tparam)),
      Seq(ValDef(FreshIdentifier("args", anyList.typed))), TupleType(Seq(BooleanType, tparam)))
  }
  lazy val updateFun = {
    val tparam = TypeParameter.fresh("T")
    val ufun = new FunDef(FreshIdentifier("update", Untyped), Seq(TypeParameterDef(tparam)),
      Seq(ValDef(FreshIdentifier("args", anyList.typed)), ValDef(FreshIdentifier("res", tparam))), tparam)
    ufun
  }

  // In the following methods, we use the globalId of the identifier of a function
  // to represent the function in the cache.
  def lookupCall(f: FunctionInvocation, valType: TypeTree) = {
    val argsList = CaseClass(anyList.typed, IntLiteral(f.tfd.fd.id.globalId) +: f.args)
    FunctionInvocation(TypedFunDef(lookupFun, Seq(valType)), Seq(argsList))
  }

  def updateCall(f: FunctionInvocation, invRes: Expr) = {
    val argsList = CaseClass(anyList.typed, IntLiteral(f.tfd.fd.id.globalId) +: f.args)
    FunctionInvocation(TypedFunDef(updateFun, Seq(invRes.getType)), Seq(argsList, invRes))
  }
}
class ExprInstrumenter(ictx: InstruContext) {
  import ExprInstrumenter._
  // Should be called only if 'expr' has to be instrumented
  // Returned Expr is always an expr of type tuple (Expr, Int)
  def tupleify(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr)(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    // When called for:
    // Op(n1,n2,n3)
    // e      = Op(n1,n2,n3)
    // subs   = Seq(n1,n2,n3)
    // recons = { Seq(newn1,newn2,newn3) => Op(newn1, newn2, newn3) }
    // This transformation should return, informally
    // Let((e1,t1), transform(n1),
    //   Let((e2,t2), transform(n2),
    //    ...
    //      Tuple(recons(e1, e2, ...), t1 + t2 + ... costOfExpr(Op)
    //    ...
    //   )
    // )
    tupleifyRecur(e, subs, recons, List(), Map())
  }

  def tupleifyRecur(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr, subeVals: List[Expr],
                    subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    implicit val currFun = ictx.currFun
    import ictx._
    //note: subs.size should be zero if e is a terminal
    if (subs.size == 0) {
      e match {
        case v @ Variable(id) =>
          val valPart = if (letIdMap.contains(id)) {
            val nid = letIdMap(id)
            if (isInstVar(nid))
              TupleSelect(nid.toVariable, 1) //this takes care of replacement
            else nid.toVariable
          } else v
          val instPart = ictx.instrumenters map (_.instrument(v, Seq()))
          Tuple(valPart +: instPart)
        case t: Terminal =>
          val instPart = ictx.instrumenters map (_.instrument(t, Seq()))
          val finalRes = Tuple(t +: instPart)
          finalRes
        case _: FunctionInvocation | _: Application => tupleifyCall(e, subeVals, subeInsts)
        // TODO: We are ignoring the construction cost of fields. Fix this.
        case _ =>
          val instexprs = ictx.instrumenters.zipWithIndex.map {
            case (menter, i) => menter.instrument(e, subeInsts.getOrElse(menter.inst, List()))
          }
          Tuple(recons(subeVals) +: instexprs)
      }
    } else {
      val currExp = subs.head
      //transform the current expression
      val transCurrExpr = transform(currExp)
      val resvar = Variable(createInstVar("e", transCurrExpr.getType))
      val eval = TupleSelect(resvar, 1)
      val instMap = insts.map { inst =>
        (inst -> (subeInsts.getOrElse(inst, List()) :+ selectInst(resvar, inst)))
      }.toMap
      //process the remaining arguments
      val recRes = tupleifyRecur(e, subs.tail, recons, subeVals :+ eval, instMap)
      Let(resvar.id, transCurrExpr, recRes)
    }
  }

  def tupleifyCall(f: Expr, subeVals: List[Expr], subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    import ictx._
    implicit val currFun = ictx.currFun
    f match {
      case fi @ FunctionInvocation(tfd @ TypedFunDef(fd, tps), args) =>
        // here, selectInst must refer to the target function, not the current function
        val selectInst = serialInst.selectInst(fd) _
        val newfd = TypedFunDef(funMap.getOrElse(fd, fd), tps map serialInst.instrumentType)
        val newFunInv = FunctionInvocation(newfd, subeVals)
        //create a variable to store the result of function invocation
        if (serialInst.instFuncs(fd)) { //this function is also instrumented
          val funres = Variable(createInstVar("e", newfd.returnType))
          val valexpr = TupleSelect(funres, 1)
          if (fd.hasLazyFieldFlag || HOMemUtil.hasMemAnnotation(fd)) {
            // here the invoked function is memoized, so we need to lookup/update the cache
            // note: the lookup cost would be included while computing the cost of the function
            val lookupres = Variable(FreshIdentifier("lr", TupleType(Seq(BooleanType, newfd.returnType)), true))
            val hitCond = TupleSelect(lookupres, 1)
            val lookupVal = TupleSelect(lookupres, 2)
            // here, we ignore the cost of the callee function completely, as if this is a val field access.
            val hitInstExprs = instrumenters.map(m =>
              m.instrument(f, subeInsts.getOrElse(m.inst, List()), Some(funres))) // cost of lookup is cost of f
            val hitCase = Tuple(lookupVal +: hitInstExprs)

            val missInstExprs = ictx.instrumenters.map { m =>
              val luCost = m.missCost() // lookup/update cost combined
              m.instrument(f, subeInsts.getOrElse(m.inst, List()) :+ Plus(luCost, selectInst(funres, m.inst)),
                Some(funres)) // note: even though calleeInst is passed, it may or may not be used.
            }
            val ur = FreshIdentifier("ur", newfd.returnType, true)
            val missCase = Let(funres.id, newFunInv, Let(ur,
              updateCall(newFunInv, valexpr), Tuple(ur.toVariable +: missInstExprs)))
            Let(lookupres.id, lookupCall(newFunInv, valexpr.getType),
              IfExpr(hitCond, hitCase, missCase))
          } else {
            val instexprs = ictx.instrumenters.map { m =>
              val calleeInst =
                if (serialInst.funcInsts(fd).contains(m.inst) && !fd.flags.contains(IsField(false))) {
                  List(selectInst(funres, m.inst))
                } else List() // ignoring fields here
              m.instrument(f, subeInsts.getOrElse(m.inst, List()) ++ calleeInst, Some(funres)) // note: even though calleeInst is passed, it may or may not be used.
            }
            Let(funres.id, newFunInv, Tuple(valexpr +: instexprs))
          }
        } else {
          val resvar = Variable(createInstVar("e", newFunInv.getType))
          val instexprs = ictx.instrumenters.map { m =>
            m.instrument(f, subeInsts.getOrElse(m.inst, List()))
          }
          Let(resvar.id, newFunInv, Tuple(resvar +: instexprs))
        }

      case Application(fterm, args) =>
        // here, selectInst must refer to the target function type, not the current function
        val ftype = fterm.getType.asInstanceOf[FunctionType]
        val selectInst = serialInst.selectInst(ftype) _
        val newApp = Application(subeVals.head, subeVals.tail)
        //create a variables to store the result of application
        if (!serialInst.instsOfLambdaType(ftype).isEmpty) { //the lambda is instrumented
          val resvar = Variable(createInstVar("e", newApp.getType))
          val valexpr = TupleSelect(resvar, 1)
          val instexprs = ictx.instrumenters.map { m =>
            m.instrument(f, subeInsts.getOrElse(m.inst, List()) ++ List(selectInst(resvar, m.inst)), Some(resvar)) // note: even though calleeInst is passed, it may or may not be used.
          }
          Let(resvar.id, newApp, Tuple(valexpr +: instexprs))
        } else {
          val resvar = Variable(createInstVar("e", newApp.getType))
          val instexprs = ictx.instrumenters.map { m =>
            m.instrument(f, subeInsts.getOrElse(m.inst, List()))
          }
          Let(resvar.id, newApp, Tuple(resvar +: instexprs))
        }
    }
  }

  /**
   * TODO: need to handle new expression trees
   */
  def transform(e: Expr)(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
    import ictx._
    implicit val currFun = ictx.currFun
    e match {
      case _ if instCall(e).isDefined =>
        serialInst.mapInstCallWithArgs(e, transform)

      // Matchcases with guards are converted to if-then-else.
      case me @ MatchExpr(scrutinee, matchCases) =>
        if (matchCases.exists(_.optGuard.isDefined)) {
          // converts match to if-then-else here.
          val condsAndRhs = for (cse <- matchCases) yield {
            val map = mapForPattern(scrutinee, cse.pattern)
            val patCond = conditionForPattern(scrutinee, cse.pattern, includeBinders = false)
            val realCond = cse.optGuard match {
              case Some(g) => patCond withCond replaceFromIDs(map, g)
              case None    => patCond
            }
            val newRhs = replaceFromIDs(map, cse.rhs)
            (realCond.toClause, newRhs)
          }
          val ite = condsAndRhs.foldRight[Expr](Error(me.getType, "Match is non-exhaustive").copiedFrom(me)) {
            case ((cond, rhs), elze) =>
              if (cond == tru) rhs else IfExpr(cond, rhs, elze)
          }
          transform(ite)
        } else {
          val transScrut = transform(scrutinee)
          val scrutRes = Variable(createInstVar("scr", transScrut.getType))
          val scrutValType = scrutRes.getType match {
            case TupleType(bases) => bases.head
            case Untyped          => serialInst.instrumentType(scrutinee.getType) // here, we may be using memoization
          }
          val matchExpr = MatchExpr(TupleSelect(scrutRes, 1),
            matchCases.map {
              case mCase @ MatchCase(pattern, guard, body) =>
                val (transPattern, bindMap) = serialInst.mapCasePattern(pattern, scrutValType) // the type of the valpart
                val transBody = transform(body)(letIdMap ++ bindMap)
                val bodyRes = Variable(createInstVar("mc", transBody.getType))
                val instExprs = ictx.instrumenters map { m =>
                  m.instrumentMatchCase(me, mCase, ictx.selectInst(bodyRes, m.inst),
                    ictx.selectInst(scrutRes, m.inst))
                }
                MatchCase(transPattern, guard,
                  Let(bodyRes.id, transBody, Tuple(TupleSelect(bodyRes, 1) +: instExprs)))
            })
          Let(scrutRes.id, transScrut, matchExpr)
        }

      case Let(i, v, b) =>
        val (ni, nv) = {
          val transv = transform(v)
          val ir = Variable(createInstVar("ir", transv.getType))
          (ir, transv)
        }

        val transformedBody = transform(b)(letIdMap + (i -> ni.id))
        val r = Variable(createInstVar("r", transformedBody.getType))
        val instexprs = instrumenters map { m =>
          m.instrument(e, List(selectInst(ni, m.inst), selectInst(r, m.inst)))
        }
        Let(ni.id, nv,
          Let(r.id, transformedBody, Tuple(TupleSelect(r, 1) +: instexprs)))

      case ife @ IfExpr(cond, th, elze) =>
        val (nifCons, condInsts) = {
          val rescond = Variable(createInstVar("c", TupleType(cond.getType +: instTypes)))
          val condInstPart = insts.map { inst => (inst -> selectInst(rescond, inst)) }.toMap
          val recons = (e1: Expr, e2: Expr) => {
            Let(rescond.id, transform(cond), IfExpr(TupleSelect(rescond, 1), e1, e2))
          }
          (recons, condInstPart)
        }
        val (nthenCons, thenInsts) = {
          val transThen = transform(th)
          val resthen = Variable(createInstVar("th", transThen.getType))
          val thInstPart = insts.map { inst => (inst -> selectInst(resthen, inst)) }.toMap
          val recons = (theninsts: List[Expr]) => {
            Let(resthen.id, transThen, Tuple(TupleSelect(resthen, 1) +: theninsts))
          }
          (recons, thInstPart)

        }
        val (nelseCons, elseInsts) = {
          val transElze = transform(elze)
          val reselse = Variable(createInstVar("el", transElze.getType))
          val elInstPart = insts.map { inst => (inst -> selectInst(reselse, inst)) }.toMap
          val recons = (einsts: List[Expr]) => {
            Let(reselse.id, transElze, Tuple(TupleSelect(reselse, 1) +: einsts))
          }
          (recons, elInstPart)
        }
        val (finalThInsts, finalElInsts) = instrumenters.foldLeft((List[Expr](), List[Expr]())) {
          case ((thinsts, elinsts), menter) =>
            val inst = menter.inst
            val (thinst, elinst) = menter.instrumentIfThenElseExpr(ife,
              Some(condInsts(inst)), Some(thenInsts(inst)), Some(elseInsts(inst)))
            (thinsts :+ thinst, elinsts :+ elinst)
        }
        val nthen = nthenCons(finalThInsts)
        val nelse = nelseCons(finalElInsts)
        nifCons(nthen, nelse)

      case l @ Lambda(args, body) => // instrument the lambda using a new context
        val lambInsts = serialInst.instsOfLambdaType(l.getType.asInstanceOf[FunctionType])
        val nbody =
          if (lambInsts.isEmpty) serialInst.mapExpr(body, letIdMap)
          else {
            (new ExprInstrumenter(new InstruContext(ictx.currFun, serialInst, lambInsts, Some(l))))(body, letIdMap)
          }
        val instexprs = instrumenters map { m => m.instrument(l, List()) } // model the time taken for constructing the lambda
        Tuple(Lambda(args, nbody) +: instexprs)

      case ClassExpr(ct, args, op) =>
        tupleify(e, args, op(serialInst.mapClassType(ct)))

      case n @ Operator(ss, recons) =>
        tupleify(e, ss, recons)

      case t: Terminal =>
        tupleify(e, Seq(), { case Seq() => t })
    }
  }

  def apply(e: Expr, paramMap: Map[Identifier, Identifier]): Expr = {
    import ictx._
    implicit val currFun = ictx.currFun
    val transformed = transform(e)(paramMap)
    val bodyId = createInstVar("bd", transformed.getType)
    val instExprs = instrumenters map { m =>
      m.instrumentBody(e, selectInst(bodyId.toVariable, m.inst))
    }
    Let(bodyId, transformed,
      Tuple(TupleSelect(bodyId.toVariable, 1) +: instExprs))
  }
}

/**
 * Implements procedures for a specific instrumentation
 */
abstract class Instrumenter(program: Program, si: SerialInstrumenter) {

  def inst: Instrumentation

  val cg = si.cg

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]]

  def functionTypesToInstrument(): Map[CompatibleType, List[Instrumentation]]

  def additionalfunctionsToAdd(): Seq[FunDef]

  def instProp(instExpr: Expr)(fd: FunDef): Option[Expr] = None

  def instrumentBody(bodyExpr: Expr, instExpr: Expr)(implicit fd: FunDef): Expr = instExpr

  def missCost() = {
    InfiniteIntegerLiteral(2)
  }

  def getRootFuncs(prog: Program = program): (Set[FunDef], Set[CompatibleType]) = {
    // go over all user-defined functions, and collect those functions with an argument less instCall in the postcondition
    // and the arguments of the instCall
    var instFuns = Set[FunDef]()
    var instTypes = Set[CompatibleType]()
    userLevelFunctions(prog) foreach {fd =>
      postTraversal{
        case fi@FunctionInvocation(_, args) if inst.isInstCall(fi) =>
          args match {
            case Seq() => instFuns += fd
            case Seq(FunctionInvocation(tfd, _)) => instFuns += tfd.fd
            case Seq(Application(fterm, _)) => instTypes += new CompatibleType(fterm.getType)
            case _ => throw new IllegalStateException("Argument of InstCall not an invocation: "+fi)
          }
        case _ =>
      }(fd.fullBody)
    }
    (instFuns, instTypes)
  }

  /**
   * Given an expression to be instrumented
   * and the instrumentation of each of its subexpressions,
   * computes an instrumentation for the procedure.
   * The sub-expressions correspond to expressions returned
   * by Expression Extractors.
   * fd is the function containing the expression `e`
   */
  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)(implicit fd: FunDef, letIdMap: Map[Identifier, Identifier]): Expr

  /**
   * Instrument procedure specialized for if-then-else
   */
  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
                               thenInst: Option[Expr], elzeInst: Option[Expr])(implicit fd: FunDef): (Expr, Expr)

  /**
   * This function is expected to combine the cost of the scrutinee,
   * the pattern matching and the expression.
   * The cost model for pattern matching is left to the user.
   * As matches with guards are converted to ifThenElse statements,
   * the user may want to make sure that the cost model for pattern
   * matching across match statements and ifThenElse statements is consistent
   */
  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
                          caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr
}