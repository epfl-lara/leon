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
  * An effect is defined as the impact that a function can have on its environment.
  * In the Leon language, there are no global variables that aren't explicit, so
  * the effect of a function is defined as the set of its parameters that are mutated
  * by executing the body. It is a conservative over-abstraction, as some update operations
  * might actually not modify the object, but this will still be considered as an
  * effect.
  *
  * There are actually a very limited number of features that rely on global state (epsilon).
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
  *
  * The EffectsAnalysis also provides functions to analyze the the mutability of a type and expression.
  * The isMutableType function need to perform a graph traversal (explore all the fields recursively
  * to find if one is mutable)
  *
  * Throughout the code, we assume that there is no aliasing. This is the global assumption made
  * in Leon for effects. Some alias analysis to check that property needs to be performed before
  * relying on the EffectsAnalysis features.
  * TODO: we might integrate the limited alias analysis for pattern matching with substitution inside here
  *       Or better, we should introduce a simple AliasAnalysis class that provide functionalities.
  */
class EffectsAnalysis {


  private val dependencies = new DependencyFinder
  private var mutableTypes: MutableMap[TypeTree, Boolean] = MutableMap.empty

  //for each fundef, the set of modified params (by index)
  //once set, the value is final and won't be modified further
  private val cachedEffects: MutableMap[FunDef, Set[Int]] = MutableMap.empty

  def apply(fd: FunDef): Set[Int] = cachedEffects.getOrElseUpdate(fd, {
    effectsAnalysis(fd)
  })

  /** Return all effects of expr
    *
    * Effects of expr are any free variables in scope (either local vars
    * already defined in the scope containing expr, or global var) that
    * are re-assigned by an operation in the expression. An effect is
    * also a mutation of an object refer by an id defined in the scope.
    *
    * This is a conservative analysis, not taking into account control-flow.
    * The set of effects is not definitely effects, but any identifier
    * not in the set will for sure have no effect.
    *
    * We are assuming no aliasing.
    */
  def apply(expr: Expr): Set[Identifier] = {
    val fds: Set[FunDef] = dependencies(expr).collect{ case (fd: FunDef) => fd }
    for(fd <- fds) effectsAnalysis(fd)
    val fdsEffects: Map[FunDef, Set[Identifier]] = cachedEffects.map{ case (fd, idx) => {
      val ids = idx.map(i => fd.params(i).id)
      (fd, ids)
    }}.toMap
    currentEffects(expr, fdsEffects)
  }



  /** Determine if the type is mutable
    *
    * In Leon, we classify types as either mutable or immutable. Immutable
    * type can be referenced freely, while mutable types must be treated with
    * care. This function uses a cache, so make sure to not update your class
    * def and use the same instance of EffectsAnalysis. It is fine to add
    * new ClassDef types on the fly, granted that they use fresh identifiers.
    */
  def isMutableType(tpe: TypeTree): Boolean = {
    def rec(tpe: TypeTree, abstractClasses: Set[ClassType]): Boolean = mutableTypes.getOrElseUpdate(tpe, tpe match {
      case (tp: TypeParameter) => tp.isMutable
      case (ct: ClassType) if abstractClasses.contains(ct) => false
      case (arr: ArrayType) => true
      case ct@CaseClassType(ccd, _) => ccd.fields.exists(vd => vd.isVar || rec(vd.getType, abstractClasses + ct))
      case (ct: ClassType) => ct.knownDescendants.exists(c => rec(c, abstractClasses + ct))
      case _ => false
    })
    rec(tpe, Set())
  }

  /** Effects at the level of types for a function
    *
    * This disregards the actual implementation of a function, and considers only
    * its type to determine a conservative abstraction of its effects.
    *
    * In theory this can be overriden to use a different behaviour.
    */
  def functionTypeEffects(ft: FunctionType): Set[Int] = {
    ft.from.zipWithIndex.flatMap{ case (vd, i) =>
      if(isMutableType(vd.getType)) Some(i) else None
    }.toSet
  }


  /*
   * Check if expr is mutating variable id. This only checks if the expression
   * is the mutation operation, and will not perform expression traversal to
   * see if a sub-expression mutates something.
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
    case Assignment(i, _) => i == id
    case _ => false
  }

  private def showFunDefWithEffect(fdsEffects: Map[FunDef, Set[Identifier]]): String =
    fdsEffects.filter(p => p._2.nonEmpty).map(p => (p._1.id, p._2)).toString

  private def findArgumentForParam(fi: FunctionInvocation, param: Identifier): Option[Expr] = {
    val index = fi.tfd.fd.params.indexWhere(vd => vd.id == param)
    if(index >= 0) Some(fi.args(index)) else None
  }

  //compute the effects of an expr, given the currently known fd effects
  //The fdsEffects params is needed as we are computing a fixpoint (due to
  //mutually recursive functions) and we want to be able to determine all effects
  //of an expression, including function calls, while still performing the fixpoint
  private def currentEffects(expr: Expr, fdsEffects: Map[FunDef, Set[Identifier]]): Set[Identifier] = {
    //println("computing effects of: " + expr)
    val freeVars = variablesOf(expr)
    val localAliases: Map[Identifier, Set[Identifier]] = freeVars.map(id => (id, computeLocalAliases(id, expr))).toMap
    val firstLevelMutated: Set[Identifier] = freeVars.filter(id => {
      val aliases = localAliases(id)
      exists(expr => aliases.exists(id => isMutationOf(expr, id)))(expr)
    })

    val allCalls: Set[FunctionInvocation] = functionCallsOf(expr)

    val secondLevelMutated: Set[Identifier] = 
      allCalls.foldLeft(Set[Identifier]())((totalEffects, fi) =>
        totalEffects ++ freeVars.intersect(invocationCurrentEffects(fi, fdsEffects))
      )

    firstLevelMutated ++ secondLevelMutated
  }

  private def invocationCurrentEffects(fi: FunctionInvocation, fdsEffects: Map[FunDef, Set[Identifier]]): Set[Identifier] = {
    val functionEffects: Set[Identifier] = fdsEffects.get(fi.tfd.fd).getOrElse(Set())
    val res = functionEffects.flatMap(id =>
      findArgumentForParam(fi, id) match {
        case Some(arg) => findReceiverId(arg)
        case None => Some(id)
      }
    )
    //println(res)
    res
  }

  //return the set of modified variables arguments to a function invocation,
  //given the effect of the fun def invoked.
  private def functionInvocationEffects(fi: FunctionInvocation, effects: Set[Int]): Seq[Identifier] = {
    fi.args.map(arg => findReceiverId(arg)).zipWithIndex.flatMap{
      case (Some(id), i) if effects.contains(i) => Some(id)
      case _ => None
    }
  }

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

  //for a given id, compute the identifiers that alias it or some part of the object refered by id
  private def computeLocalAliases(id: Identifier, body: Expr): Set[Identifier] = {
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


  private def findReceiverId(o: Expr): Option[Identifier] = o match {
    case Variable(id) => Some(id)
    case CaseClassSelector(_, e, _) => findReceiverId(e)
    case AsInstanceOf(e, ct) => findReceiverId(e)
    case ArraySelect(a, _) => findReceiverId(a)
    case _ => None
  }

}
