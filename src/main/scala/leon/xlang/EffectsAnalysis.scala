package leon
package xlang

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import purescala.DependencyFinder
import xlang.Expressions._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}


/** Provides effect analysis for full Leon language
  *
  * This holds state for caching the current state of the analysis, so if
  * you modify your program you may want to create a new EffectsAnalysis
  * instance.
  *
  * You can use it lazily by only querying effects for the functions you need.
  * The internals make sure to compute only the part of the dependencies graph
  * that is needed to get the effect of the function.
  *
  * An effect is defined as the impact that a funcion can have on its environment.
  * In the Leon language, there are no global variables that aren't explicit, so
  * the effect of a function is defined as the set of its parameters that are mutated
  * by executing the body. It is a conservative over-abstraction, as some update operations
  * might actually not modify the object, but this will still be considered as an
  * effect. This is in contrast to the upcomming @pure instruction, that will actually
  * emit VC to prove that the body does not modify the parameter, even with the presence
  * of mutation operators.
  *
  * There are actually a very limited number of features relying on global state (epsilon).
  * EffectsAnalysis will not take such effects into account. You need to make sure the
  * program either does not rely on epsilon, or has been rewriting with the IntroduceGlobalStatePhase
  * phase that introduce any global state explicitly as function parameters. In the future,
  * if we do end up supporting global variables, it is likely that we will rely on another
  * phase to introduce that global state explicitly into the list of parameters of functions
  * that make use of it.
  *
  * An effect is detected by a FieldAssignment to one of the parameters that are mutable. It 
  * can come from transitively calling a function that perform a field assignment as well. 
  * If the function uses higher-order functions that take mutable types as parameters, they
  * will be conservatively assumed to perform an effect as well. A function type is not by itself
  * a mutable type, but if it is applied on a mutable type that is taken as a parameter as well,
  * it will be detected as an effect by the EffectsAnalysis. 
  * TODO: maybe we could have "conditional effects", effects depending on the effects of the lambda.
  */
class EffectsAnalysis {

  private val dependencies = new DependencyFinder


  //for each fundef, the set of modified params (by index)
  //once set, the value is final and won't be modified further
  private val cachedEffects: MutableMap[FunDef, Set[Int]] = MutableMap.empty

  def apply(fd: FunDef): Set[Int] = cachedEffects.getOrElseUpdate(fd, {
    effectsAnalysis(fd)
  })

  /*
   * compute effects for each function that from depends on, including any nested
   * functions (LetDef).
   * While computing effects for from, it might have to compute transitive effects
   * of dependencies. It will update the global effects map while doing so.
   */
  private def effectsAnalysis(from: FunDef): Set[Int] = {

    //all the FunDef to consider to compute the effects of from
    val fds: Set[FunDef] = dependencies(from).collect{ case (fd: FunDef) => fd } + from

    //currently computed effects (incremental)
    var effects: Map[FunDef, Set[Int]] = Map()//cachedEffects.filterKeys(fds.contains)
    //missing dependencies for a function for its effects to be complete
    var missingEffects: Map[FunDef, Set[FunctionInvocation]] = Map()

    def effectsFullyComputed(fd: FunDef): Boolean = !missingEffects.isDefinedAt(fd)

    for {
      fd <- fds
    } {
      cachedEffects.get(fd) match {
        case Some(efcts) =>
          effects += (fd -> efcts)
        case None =>
          fd.body match {
            case None =>
              effects += (fd -> Set())
            case Some(body) => {
              val mutableParams = fd.params.filter(vd => isMutableType(vd.getType))
              val localAliases: Map[ValDef, Set[Identifier]] = mutableParams.map(vd => (vd, computeLocalAliases(vd.id, body))).toMap
              val mutatedParams = mutableParams.filter(vd => exists(expr => localAliases(vd).exists(id => isMutationOf(expr, id)))(body))
              val mutatedParamsIndices = fd.params.zipWithIndex.flatMap{
                case (vd, i) if mutatedParams.contains(vd) => Some(i)
                case _ => None
              }.toSet
              effects = effects + (fd -> mutatedParamsIndices)

              val missingCalls: Set[FunctionInvocation] = functionCallsOf(body).filterNot(fi => fi.tfd.fd == fd)
              if(missingCalls.nonEmpty)
                missingEffects += (fd -> missingCalls)
            }
          }
      }
    }

    def rec(): Unit = {
      val previousMissingEffects = missingEffects

      for{ (fd, calls) <- missingEffects } {
        var newMissingCalls: Set[FunctionInvocation] = calls
        for(fi <- calls) {
          val mutatedArgs = invocEffects(fi)
          val mutatedFunParams: Set[Int] = fd.params.zipWithIndex.flatMap{
            case (vd, i) if mutatedArgs.contains(vd.id) => Some(i)
            case _ => None
          }.toSet
          effects += (fd -> (effects(fd) ++ mutatedFunParams))

          if(effectsFullyComputed(fi.tfd.fd)) {
            newMissingCalls -= fi
          }
        }
        if(newMissingCalls.isEmpty)
          missingEffects = missingEffects - fd
        else
          missingEffects += (fd -> newMissingCalls)
      }

      if(missingEffects != previousMissingEffects) {
        rec()
      }
    }

    def invocEffects(fi: FunctionInvocation): Set[Identifier] = {
      //TODO: the require should be fine once we consider nested functions as well
      //require(effects.isDefinedAt(fi.tfd.fd)
      val mutatedParams: Set[Int] = effects.get(fi.tfd.fd).getOrElse(Set())
      functionInvocationEffects(fi, mutatedParams).toSet
    }

    rec()

    effects.foreach{ case (fd, efcts) => if(!cachedEffects.isDefinedAt(fd)) cachedEffects(fd) = efcts }

    effects(from)
  }

  //convert a function type with mutable parameters, into a function type
  //that returns the mutable parameters. This makes explicit all possible
  //effects of the function. This should be used for higher order functions
  //declared as parameters.
  def makeFunctionTypeExplicit(tpe: FunctionType): FunctionType = {
    val newReturnTypes = tpe.from.filter(t => isMutableType(t))
    if(newReturnTypes.isEmpty)
      tpe
    else {
      FunctionType(tpe.from, TupleType(tpe.to +: newReturnTypes))
    }
  }

  def functionTypeEffects(ft: FunctionType): Set[Int] = {
    ft.from.zipWithIndex.flatMap{ case (vd, i) =>
      if(isMutableType(vd.getType)) Some(i) else None
    }.toSet
  }

  //for a given id, compute the identifiers that alias it or some part of the object refered by id
  def computeLocalAliases(id: Identifier, body: Expr): Set[Identifier] = {
    def pre(expr: Expr, ids: Set[Identifier]): Set[Identifier] = expr match {
      case l@Let(i, Variable(v), _) if ids.contains(v) => ids + i
      case m@MatchExpr(Variable(v), cses) if ids.contains(v) => {
        val newIds = cses.flatMap(mc => mc.pattern.binders)
        ids ++ newIds
      }
      case e => ids
    }
    def combiner(e: Expr, ctx: Set[Identifier], ids: Seq[Set[Identifier]]): Set[Identifier] = ctx ++ ids.toSet.flatten + id
    val res = preFoldWithContext(pre, combiner)(body, Set(id))
    res
  }


  def checkAliasing(fd: FunDef)(ctx: LeonContext): Unit = {
    def checkReturnValue(body: Expr, bindings: Set[Identifier]): Unit = {
      getReturnedExpr(body).foreach{
        case expr if isMutableType(expr.getType) => 
          findReceiverId(expr).foreach(id =>
            if(bindings.contains(id))
              ctx.reporter.fatalError(expr.getPos, "Cannot return a shared reference to a mutable object: " + expr)
          )
        case _ => ()
      }
    }

    if(fd.canBeField && isMutableType(fd.returnType))
      ctx.reporter.fatalError(fd.getPos, "A global field cannot refer to a mutable object")
    
    fd.body.foreach(bd => {
      val params = fd.params.map(_.id).toSet
      checkReturnValue(bd, params)
      preMapWithContext[Set[Identifier]]((expr, bindings) => expr match {
        case l@Let(id, v, b) if isMutableType(v.getType) => {
          if(!isExpressionFresh(v))
            ctx.reporter.fatalError(v.getPos, "Illegal aliasing: " + v)
          (None, bindings + id)
        }
        case l@LetVar(id, v, b) if isMutableType(v.getType) => {
          if(!isExpressionFresh(v))
            ctx.reporter.fatalError(v.getPos, "Illegal aliasing: " + v)
          (None, bindings + id)
        }
        case l@LetDef(fds, body) => {
          fds.foreach(fd => fd.body.foreach(bd => checkReturnValue(bd, bindings)))
          (None, bindings)
        }

        case _ => (None, bindings)
      })(bd, params)
    })
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


  private def findReceiverId(o: Expr): Option[Identifier] = o match {
    case Variable(id) => Some(id)
    case CaseClassSelector(_, e, _) => findReceiverId(e)
    case AsInstanceOf(e, ct) => findReceiverId(e)
    case ArraySelect(a, _) => findReceiverId(a)
    case _ => None
  }


  private def isMutableType(tpe: TypeTree, abstractClasses: Set[ClassType] = Set()): Boolean = tpe match {
    case (ct: ClassType) if abstractClasses.contains(ct) => false
    case (arr: ArrayType) => true
    case ct@CaseClassType(ccd, _) => ccd.fields.exists(vd => vd.isVar || isMutableType(vd.getType, abstractClasses + ct))
    case (ct: ClassType) => ct.knownDescendants.exists(c => isMutableType(c, abstractClasses + ct))
    case _ => false
  }


  /*
   * Check if expr is mutating variable id
   */
  private def isMutationOf(expr: Expr, id: Identifier): Boolean = expr match {
    case ArrayUpdate(o, _, _) => findReceiverId(o).exists(_ == id)
    case FieldAssignment(obj, _, _) => findReceiverId(obj).exists(_ == id)
    case Application(callee, args) => {
      val ft@FunctionType(_, _) = callee.getType
      val effects = functionTypeEffects(ft)
      args.map(findReceiverId(_)).zipWithIndex.exists{
        case (Some(argId), index) => argId == id && effects.contains(index)
        case _ => false
      }
    }
    case _ => false
  }

  //return the set of modified variables arguments to a function invocation,
  //given the effect of the fun def invoked.
  private def functionInvocationEffects(fi: FunctionInvocation, effects: Set[Int]): Seq[Identifier] = {
    fi.args.map(arg => findReceiverId(arg)).zipWithIndex.flatMap{
      case (Some(id), i) if effects.contains(i) => Some(id)
      case _ => None
    }
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


  def deepCopy(rec: Expr, nv: Expr): Expr = {
    rec match {
      case CaseClassSelector(_, r, id) =>
        val sub = copy(r, id, nv)
        deepCopy(r, sub)
      case as@ArraySelect(a, index) =>
        deepCopy(a, ArrayUpdated(a, index, nv).setPos(as))
      case expr => nv
    }
  }

  private def copy(cc: Expr, id: Identifier, nv: Expr): Expr = {
    val ct@CaseClassType(ccd, _) = cc.getType
    val newFields = ccd.fields.map(vd =>
      if(vd.id == id)
        nv
      else
        CaseClassSelector(CaseClassType(ct.classDef, ct.tps), cc, vd.id)
    )
    CaseClass(CaseClassType(ct.classDef, ct.tps), newFields).setPos(cc.getPos)
  }


  /*
   * A fresh expression is an expression that is newly created
   * and does not share memory with existing values and variables.
   *
   * If the expression is made of existing immutable variables (Int or
   * immutable case classes), it is considered fresh as we consider all
   * non mutable objects to have a value-copy semantics.
   *
   * It turns out that an expression of non-mutable type is always fresh,
   * as it can not contains reference to a mutable object, by definition
   */
  private def isExpressionFresh(expr: Expr): Boolean = {
    !isMutableType(expr.getType) || (expr match {
      case v@Variable(_) => !isMutableType(v.getType)
      case CaseClass(_, args) => args.forall(arg => isExpressionFresh(arg))

      case FiniteArray(elems, default, _) => elems.forall(p => isExpressionFresh(p._2)) && default.forall(isExpressionFresh)

      //function invocation always return a fresh expression, by hypothesis (global assumption)
      case FunctionInvocation(_, _) => true

      //ArrayUpdated returns a mutable array, which by definition is a clone of the original
      case ArrayUpdated(_, _, _) => true

      //any other expression is conservately assumed to be non-fresh if
      //any sub-expression is non-fresh (i.e. an if-then-else with a reference in one branch)
      case Operator(args, _) => args.forall(arg => isExpressionFresh(arg))
    })
  }

}
