package leon
package invariant.structure

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import java.io._
import solvers.z3._
import invariant.engine._
import invariant.util._
import leon.solvers.Model
import Util._
import PredicateUtil._
import TVarFactory._
import ExpressionTransformer._
import evaluators._
import invariant.factories._

/**
 * Data associated with a call
 */
class CallData(val guard : Variable, val parents: List[FunDef])

object Formula {
  val debugUnflatten = false
  // a context for creating blockers
  val blockContext = newContext
}

/**
 * Representation of an expression as a set of implications.
 * 'initexpr' is required to be in negation normal form and And/Ors have been pulled up
 * TODO: optimize the representation so that we use fewer guards.
 */
class Formula(val fd: FunDef, initexpr: Expr, ctx: InferenceContext) {

  import Formula._

  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val useImplies = false

  val combiningOp = if(useImplies) Implies.apply _ else Equals.apply _
  protected var disjuncts = Map[Variable, Seq[Constraint]]() //a mapping from guards to conjunction of atoms
  protected var conjuncts = Map[Variable, Expr]() //a mapping from guards to disjunction of atoms
  private var callDataMap = Map[Call, CallData]() //a mapping from a 'call' to the 'guard' guarding the call plus the list of transitive callers of 'call'
  private var paramBlockers = Set[Variable]()

  val firstRoot : Variable = addConstraints(initexpr, List(fd))._1
  protected var roots : Seq[Variable] = Seq(firstRoot) //a list of roots, the formula is a conjunction of formula of each root

  def disjunctsInFormula = disjuncts

  def callData(call: Call) : CallData = callDataMap(call)

  //return the root variable and the sequence of disjunct guards added
  //(which includes the root variable incase it respresents a disjunct)
  def addConstraints(ine: Expr, callParents : List[FunDef]) : (Variable, Seq[Variable]) = {

    var newDisjGuards = Seq[Variable]()

    def getCtrsFromExprs(guard: Variable, exprs: Seq[Expr]) : Seq[Constraint] = {
      var break = false
      exprs.foldLeft(Seq[Constraint]())((acc, e) => {
        if (break) acc
        else {
          val ctr = ConstraintUtil.createConstriant(e)
          ctr match {
            case BoolConstraint(BooleanLiteral(true)) => acc
            case BoolConstraint(BooleanLiteral(false)) => {
              break = true
              Seq(ctr)
            }
            case call@Call(_,_) => {

              if(callParents.isEmpty)
                throw new IllegalArgumentException("Parent not specified for call: "+ctr)
              else {
                callDataMap += (call -> new CallData(guard, callParents))
              }
              acc :+ call
            }
            case _ => acc :+ ctr
          }
        }
      })
    }

    /**
     * Creates disjunct of the form b == exprs and updates the necessary mutable states
     */
    def addToDisjunct(exprs: Seq[Expr], isTemplate: Boolean) = {
      val g = createTemp("b", BooleanType, blockContext).toVariable
      newDisjGuards :+= g
      val ctrs = getCtrsFromExprs(g, exprs)
      disjuncts += (g -> ctrs)
      if(isTemplate)
          paramBlockers += g
      g
    }

    val f1 = simplePostTransform {
      case e@Or(args) => {
        val newargs = args.map {
          case arg@(v: Variable) if (disjuncts.contains(v)) => arg
          case v: Variable if (conjuncts.contains(v)) => throw new IllegalStateException("or gaurd inside conjunct: " + e + " or-guard: " + v)
          case arg => {
            val atoms = arg match {
              case And(atms) => atms
              case _ => Seq(arg)
            }
            val g = addToDisjunct(atoms, !getTemplateIds(arg).isEmpty)
            //println(s"creating a new OR blocker $g for "+atoms)
            g
          }
        }
        //create a temporary for Or
        val gor = createTemp("b", BooleanType, blockContext).toVariable
        val newor = createOr(newargs)
        conjuncts += (gor -> newor)
        gor
      }
      case e@And(args) => {
        //if the expression has template variables then we separate it using guards
        val (nonparams, params) = args.partition(getTemplateIds(_).isEmpty)
        val newargs =
          if (!params.isEmpty) {
            val g = addToDisjunct(params, true)
            //println(s"creating a new Temp blocker $g for "+arg)
            paramBlockers += g
            g +: nonparams
          } else nonparams
        createAnd(newargs)
      }
      case e => e
    }(ExpressionTransformer.simplify(simplifyArithmetic(
        //TODO: this is a hack as of now. Fix this.
        //Note: it is necessary to convert real literals to integers since the linear constraint cannot handle real literals
        if(ctx.usereals) ExpressionTransformer.FractionalLiteralToInt(ine)
        else ine
        )))

    val rootvar = f1 match {
      case v: Variable if(conjuncts.contains(v)) => v
      case v: Variable if(disjuncts.contains(v)) => throw new IllegalStateException("f1 is a disjunct guard: "+v)
      case _ => {
        val atoms = f1 match {
          case And(atms) => atms
          case _ => Seq(f1)
        }
        val g = addToDisjunct(atoms, !getTemplateIds(f1).isEmpty)
        g
      }
    }
    (rootvar, newDisjGuards)
  }

  //'satGuard' is required to a guard variable
  def pickSatDisjunct(startGaurd : Variable, model: LazyModel): Seq[Constraint] = {

    def traverseOrs(gd: Variable, model: LazyModel): Seq[Variable] = {
      val e @ Or(guards) = conjuncts(gd)
      //pick one guard that is true
      val guard = guards.collectFirst { case g @ Variable(id) if (model(id) == tru) => g }
      if (guard.isEmpty)
        throw new IllegalStateException("No satisfiable guard found: " + e)
      guard.get +: traverseAnds(guard.get, model)
    }

    def traverseAnds(gd: Variable, model: LazyModel): Seq[Variable] = {
      val ctrs = disjuncts(gd)
      val guards = ctrs.collect {
        case BoolConstraint(v @ Variable(_)) if (conjuncts.contains(v) || disjuncts.contains(v)) => v
      }
      if (guards.isEmpty) Seq()
      else {
        guards.foldLeft(Seq[Variable]())((acc, g) => {
          if (model(g.id) != tru)
            throw new IllegalStateException("Not a satisfiable guard: " + g)

          if (conjuncts.contains(g))
            acc ++ traverseOrs(g, model)
          else {
            acc ++ (g +: traverseAnds(g, model))
          }
        })
      }
    }
    //if startGuard is unsat return empty
    if (model(startGaurd.id) == fls) Seq()
    else {
      val satGuards = if (conjuncts.contains(startGaurd)) traverseOrs(startGaurd, model)
      else (startGaurd +: traverseAnds(startGaurd, model))
      satGuards.flatMap(g => disjuncts(g))
    }
  }

  /**
   * 'neweexpr' is required to be in negation normal form and And/Ors have been pulled up
   */
  def conjoinWithDisjunct(guard: Variable, newexpr: Expr, callParents: List[FunDef]) : (Variable, Seq[Variable]) = {
     val (exprRoot, newGaurds) = addConstraints(newexpr, callParents)
     //add 'newguard' in conjunction with 'disjuncts(guard)'
     val ctrs = disjuncts(guard)
     disjuncts -= guard
     disjuncts += (guard -> (BoolConstraint(exprRoot) +: ctrs))
     (exprRoot, newGaurds)
  }

  def conjoinWithRoot(newexpr: Expr, callParents: List[FunDef]): (Variable, Seq[Variable]) = {
    val (exprRoot, newGaurds) = addConstraints(newexpr, callParents)
    roots :+= exprRoot
    (exprRoot, newGaurds)
  }

  def templateIdsInFormula = paramBlockers.flatMap { g =>
    getTemplateIds(createAnd(disjuncts(g).map(_.toExpr)))
  }.toSet

  /**
   * The first return value is param part and the second one is the
   * non-parametric part
   */
  def splitParamPart : (Expr, Expr) = {
    val paramPart = paramBlockers.toSeq.map{ g =>
      combiningOp(g,createAnd(disjuncts(g).map(_.toExpr)))
    }
    val rest = disjuncts.collect {
      case (g, ctrs) if !paramBlockers(g) =>
        combiningOp(g, createAnd(ctrs.map(_.toExpr)))
    }.toSeq
    val conjs = conjuncts.map((entry) => combiningOp(entry._1, entry._2)).toSeq ++ roots
    (createAnd(paramPart), createAnd(rest ++ conjs))
  }

  def toExpr : Expr={
    val disjs = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      combiningOp(g, createAnd(ctrs.map(_.toExpr)))
    }).toSeq
    val conjs = conjuncts.map((entry) => combiningOp(entry._1, entry._2)).toSeq
    createAnd(disjs ++ conjs ++ roots)
  }

  /**
   * Creates an unflat expr of the non-param part,
   * and returns a constructor for the flat model from unflat models
   */
  def toUnflatExpr = {
    val paramPart = paramBlockers.toSeq.map{ g =>
      combiningOp(g,createAnd(disjuncts(g).map(_.toExpr)))
    }
    // compute variables used in more than one disjunct
    var uniqueVars = Set[Identifier]()
    var sharedVars = Set[Identifier]()
    var freevars = Set[Identifier]()
    disjuncts.foreach{
      case (g, ctrs) =>
        val fvs = ctrs.flatMap(c => variablesOf(c.toExpr)).toSet
        val candUniques = fvs -- sharedVars
        val newShared = uniqueVars.intersect(candUniques)
        freevars ++= fvs
        sharedVars ++= newShared
        uniqueVars = (uniqueVars ++ candUniques) -- newShared
    }
    // unflatten rest
    var flatIdMap = Map[Identifier, Expr]()
    val unflatRest = (disjuncts collect {
      case (g, ctrs) if !paramBlockers(g) =>
        val rhs = createAnd(ctrs.map(_.toExpr))
        val (unflatRhs, idmap) = simpleUnflattenWithMap(rhs, sharedVars, includeFuns = false)
        // sanity checks
        if (debugUnflatten) {
          val rhsvars = variablesOf(rhs)
          if(!rhsvars.filter(TemplateIdFactory.IsTemplateIdentifier).isEmpty)
            throw new IllegalStateException(s"Non-param part has template identifiers ${toString}")
          val seenKeys = flatIdMap.keySet.intersect(rhsvars)
          if (!seenKeys.isEmpty)
            throw new IllegalStateException(s"flat ids used across clauses $seenKeys in ${toString}")
        }
        flatIdMap ++= idmap
        combiningOp(g, unflatRhs)
    }).toSeq
    val modelCons = (m: Model, eval: DefaultEvaluator) => new FlatModel(freevars, flatIdMap, m, eval)
    val conjs = conjuncts.map{ case(g,rhs) => combiningOp(g, rhs) }.toSeq ++ roots
    (createAnd(paramPart), createAnd(unflatRest ++ conjs), modelCons)
  }

  //unpack the disjunct and conjuncts by removing all guards
  def eliminateBlockers : Expr = {
    //replace all conjunct guards in disjuncts by their mapping
    val disjs : Map[Expr,Expr] = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      val newctrs = ctrs.map {
        case BoolConstraint(g@Variable(_)) if conjuncts.contains(g) => conjuncts(g)
        case ctr@_ => ctr.toExpr
      }
      (g, createAnd(newctrs))
    })
    val rootexprs = roots.map {
      case g@Variable(_) if conjuncts.contains(g) => conjuncts(g)
      case e@_ => e
    }
    //replace every guard in the 'disjs' by its disjunct. DO this as long as every guard is replaced in every disjunct
    var unpackedDisjs = disjs
    var replacedGuard = true
    //var removeGuards = Seq[Variable]()
    while(replacedGuard) {
      replacedGuard = false

      val newDisjs = unpackedDisjs.map(entry => {
        val (g,d) = entry
        val guards = variablesOf(d).collect{ case id@_ if disjuncts.contains(id.toVariable) => id.toVariable }
        if (guards.isEmpty) entry
        else {
          replacedGuard = true
          //removeGuards ++= guards
          (g, replace(unpackedDisjs, d))
        }
      })
      unpackedDisjs = newDisjs
    }
    //replace all the 'guards' in root using 'unpackedDisjs'
    replace(unpackedDisjs, createAnd(rootexprs))
  }

  override def toString : String = {
    val disjStrs = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      simplifyArithmetic(combiningOp(g, createAnd(ctrs.map(_.toExpr)))).toString
    }).toSeq
    val conjStrs = conjuncts.map((entry) => combiningOp(entry._1, entry._2).toString).toSeq
    val rootStrs = roots.map(_.toString)
    (disjStrs ++ conjStrs ++ rootStrs).foldLeft("")((acc,str) => acc + "\n" + str)
  }

  /**
   * Functions for stats
   */
  def atomsCount = disjuncts.map(_._2.size).sum + conjuncts.map(i => atomNum(i._2)).sum
  def funsCount = disjuncts.map(_._2.filter(_.isInstanceOf[Call]).size).sum

  /**
   * Functions solely used for debugging
   */
  import solvers.SimpleSolverAPI
  def checkUnflattening(tempMap: Map[Expr, Expr], sol: SimpleSolverAPI, eval: DefaultEvaluator) = {
    // solve unflat formula
    val (temp, rest, modelCons) = toUnflatExpr
    val packedFor = TemplateInstantiator.instantiate(And(Seq(rest, temp)), tempMap)
    val (unflatSat, unflatModel) = sol.solveSAT(packedFor)
    // solve flat formula (using the same values for the uncompressed vars)
    val flatVCInst = simplifyArithmetic(TemplateInstantiator.instantiate(toExpr, tempMap))
    val modelExpr = SolverUtil.modelToExpr(unflatModel)
    val (flatSat, flatModel) = sol.solveSAT(And(flatVCInst, modelExpr))
    //println("Formula: "+unpackedFor)
    //println("packed formula: "+packedFor)
    val satdisj =
      if (unflatSat == Some(true))
        Some(pickSatDisjunct(firstRoot, new SimpleLazyModel(unflatModel)))
      else None
    if (unflatSat != flatSat) {
      if (satdisj.isDefined) {
        val preds = satdisj.get.filter { ctr =>
          if (getTemplateIds(ctr.toExpr).isEmpty) {
            val exp = And(Seq(ctr.toExpr, modelExpr))
            sol.solveSAT(exp)._1 == Some(false)
          } else false
        }
        println(s"Conflicting preds: ${preds.map(_.toExpr)}")
      }
      throw new IllegalStateException(s"VC produces different result with flattening: unflatSat: $unflatSat flatRes: $flatSat")
    } else {
      if (satdisj.isDefined) {
        // print all differences between the models (only along the satisfiable path, values of other variables may not be computable)
        val satExpr = createAnd(satdisj.get.map(_.toExpr))
        val lazyModel = modelCons(unflatModel, eval)
        val allvars = variablesOf(satExpr)
        val elimIds = allvars -- variablesOf(packedFor)
        val diffs = allvars.filterNot(TemplateIdFactory.IsTemplateIdentifier).flatMap {
          case id if !flatModel.isDefinedAt(id) =>
            println("Did not find a solver model for: " + id + " elimIds: " + elimIds(id))
            Seq()
          case id if lazyModel(id) != flatModel(id) =>
            println(s"diff $id : flat: ${lazyModel(id)} solver: ${flatModel(id)}" + " elimIds: " + elimIds(id))
            Seq(id)
          case _ => Seq()
        }
        if (!diffs.isEmpty)
          throw new IllegalStateException("Model do not agree on diffs: " + diffs)
      }
    }
  }
}
