/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.structure

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import invariant.engine._
import invariant.util._
import solvers.Model
import Util._
import PredicateUtil._
import TVarFactory._
import ExpressionTransformer._
import invariant.factories._
import evaluators._
import EvaluationResults._

/**
 * Data associated with a call.
 * @param inSpec true if the call (transitively) made within specifications
 */
class CallData(val guard : Variable, val parents: List[FunDef], val inSpec: Boolean)

object Formula {
  val debugUnflatten = false
  val dumpUnflatFormula = false
  // a context for creating blockers
  val blockContext = newContext
}

/**
 * Representation of an expression as a set of implications.
 * 'initexpr' is required to be in negation normal form and And/Ors have been pulled up
 * TODO: optimize the representation so that we use fewer guards.
 * @param initSpecCalls when specified it optimizes the handling of calls made in the specification.
 */
class Formula(val fd: FunDef, initexpr: Expr, ctx: InferenceContext, initSpecCalls: Set[Expr] = Set()) {

  import Formula._

  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val useImplies = false // note: we have to use equality for 'cond' blockers (no matter what!)

  val combiningOp = if(useImplies) Implies.apply _ else Equals.apply _
  protected var disjuncts = Map[Variable, Seq[Constraint]]() //a mapping from guards to conjunction of atoms
  protected var conjuncts = Map[Variable, Expr]() //a mapping from guards to disjunction of atoms
  private var paramBlockers = Set[Variable]()
  private var callDataMap = Map[Call, CallData]() //a mapping from a 'call' to the 'guard' guarding the call plus the list of transitive callers of 'call'

  val firstRoot: Variable = addConstraints(initexpr, List(fd), c => initSpecCalls(c.toExpr))._1
  protected var roots : Seq[Variable] = Seq(firstRoot) //a list of roots, the formula is a conjunction of formula of each root

  def disjunctsInFormula = disjuncts

  def callData(call: Call) : CallData = callDataMap(call)

  //return the root variable and the sequence of disjunct guards added
  //(which includes the root variable incase it respresents a disjunct)
  def addConstraints(ine: Expr, callParents: List[FunDef], inSpec: Call => Boolean): (Variable, Seq[Variable]) = {
    def atoms(e: Expr) = e match {
      case And(atms) => atms
      case _         => Seq(e)
    }
    var newDisjGuards = Seq[Variable]()
    var condBlockers = Map[Variable, (Variable, Variable)]() // a mapping from condition constraint to then and else blockers

    def getCtrsFromExprs(guard: Variable, exprs: Seq[Expr]): Seq[Constraint] = {
      var break = false
      exprs.foldLeft(Seq[Constraint]()) {
        case (acc, _) if break => acc
        case (acc, ife @ IfExpr(cond: Variable, th, elze)) =>
          val (thBlock, elseBlock) = condBlockers(cond)
          acc :+ ITE(BoolConstraint(cond), BoolConstraint(thBlock) +: getCtrsFromExprs(thBlock, atoms(th)),
            BoolConstraint(elseBlock) +: getCtrsFromExprs(elseBlock, atoms(elze)))
        case (acc, e) =>
          ConstraintUtil.createConstriant(e) match {
            case BoolConstraint(BooleanLiteral(true)) => acc
            case fls @ BoolConstraint(BooleanLiteral(false)) =>
              break = true
              Seq(fls)
            case call @ Call(_, _) =>
              if (callParents.isEmpty) throw new IllegalArgumentException("Parent not specified for call: " + call)
              else callDataMap += (call -> new CallData(guard, callParents, inSpec(call)))
              acc :+ call
            case ctr => acc :+ ctr
          }
      }
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
    def rec(e: Expr)(implicit insideOperation: Boolean): Expr =  e match {
      case Or(args) if !insideOperation =>
        val newargs = (args map rec).map {
          case v: Variable if disjuncts.contains(v) => v
          case v: Variable if conjuncts.contains(v) => throw new IllegalStateException("or gaurd inside conjunct: " + e + " or-guard: " + v)
          case arg =>
            val g = addToDisjunct(atoms(arg), !getTemplateIds(arg).isEmpty)
            //println(s"creating a new OR blocker $g for "+atoms)
            g
        }
        val gor = createTemp("b", BooleanType, blockContext).toVariable
        val newor = createOr(newargs)
        //println("Creating or const: "+(gor -> newor))
        conjuncts += (gor -> newor)
        gor

      case And(args) =>
        //if the expression has template variables then we separate it using guards
        val (nonparams, params) = (args map rec).partition(getTemplateIds(_).isEmpty)
        val newargs =
          if (!params.isEmpty)
            addToDisjunct(params, true) +: nonparams
          else nonparams
        createAnd(newargs)

      case e : IfExpr =>
        val (con, th, elze) = (rec(e.cond)(true), rec(e.thenn)(false), rec(e.elze)(false))
        if(!isAtom(con) || !getTemplateIds(con).isEmpty)
          throw new IllegalStateException(s"Condition of ifexpr is not an atom: $e")
       // create condition and anti-condition blockers
       val ncond = addToDisjunct(Seq(con), false)
       val thBlock = addToDisjunct(Seq(), false)
       val elseBlock = addToDisjunct(Seq(), false)
       condBlockers += (ncond -> (thBlock, elseBlock))
       // normalize thn and elze
       val trans = (e: Expr) => {
         if(getTemplateIds(e).isEmpty) e
         else addToDisjunct(atoms(e), true)
       }
       IfExpr(ncond, trans(th), trans(elze))

      case Operator(args, op) =>
        op(args.map(rec(_)(true)))
    }
    val f1 = simplifyByConstructors(rec(ExpressionTransformer.simplify(simplifyArithmetic(
        //TODO: this is a hack as of now. Fix this.
        //Note: it is necessary to convert real literals to integers since the linear constraint cannot handle real literals
        if(ctx.usereals) ExpressionTransformer.FractionalLiteralToInt(ine)
        else ine
        )))(false))
    val rootvar = f1 match {
      case v: Variable if(conjuncts.contains(v)) => v
      case v: Variable if(disjuncts.contains(v)) => throw new IllegalStateException("f1 is a disjunct guard: "+v)
      case _ => addToDisjunct(atoms(f1), !getTemplateIds(f1).isEmpty)
    }
    (rootvar, newDisjGuards)
  }

  def pickSatDisjunct(startGaurd : Variable, model: LazyModel, tmplModel: Map[Identifier, Expr], eval: DefaultEvaluator): Seq[Constraint] = {

    def traverseOrs(ine: Expr): Seq[Constraint] = {
      val Or(guards) = ine
      val guard = guards.collectFirst { case g @ Variable(id) if (model(id) == tru) => g } //pick one guard that is true
      if (guard.isEmpty)
        throw new IllegalStateException("No satisfiable guard found: " + ine)
      BoolConstraint(guard.get) +: traverseAnds(disjuncts(guard.get))
    }
    def traverseAnds(inctrs: Seq[Constraint]): Seq[Constraint] =
      inctrs.foldLeft(Seq[Constraint]()) {
        case (acc, ITE(BoolConstraint(c: Variable), ths, elzes)) =>
          val conds = disjuncts(c) // here, cond it guaranteed to be an atom
          assert(conds.size <= 1)
          val ctrs =
            if (model(c.id) == tru)
              conds ++ traverseAnds(ths)
            else {
              val condCtr = conds match {
                case Seq(bc: BoolConstraint) => BoolConstraint(Not(bc.toExpr))
                case Seq(lc: LinearTemplate) => lc.pickSatDisjunctOfNegation(model, tmplModel, eval)
                case Seq(adteq: ADTConstraint) if adteq.comp =>
                  adteq.toExpr match {
                    case Not(eq) => ADTConstraint(eq)
                    case eq      => ADTConstraint(Not(eq))
                  }
              }
              condCtr +: traverseAnds(elzes)
            }
          acc ++ ctrs
        case (acc, elt: ExtendedConstraint) =>
          acc :+ elt.pickSatDisjunct(model, tmplModel, eval)
        case (acc, ctr @ BoolConstraint(v: Variable)) if conjuncts.contains(v) => //assert(model(v.id) == tru)
          acc ++ (ctr +: traverseOrs(conjuncts(v)))
        case (acc, ctr @ BoolConstraint(v: Variable)) if disjuncts.contains(v) => //assert(model(v.id) == tru)
          acc ++ (ctr +: traverseAnds(disjuncts(v)))
        case (acc, ctr) => acc :+ ctr
      }
    val path =
      if (model(startGaurd.id) == fls) Seq() //if startGuard is unsat return empty
      else {
        if (conjuncts.contains(startGaurd))
          traverseOrs(conjuncts(startGaurd))
        else
          BoolConstraint(startGaurd) +: traverseAnds(disjuncts(startGaurd))
      }
    /*println("Path: " + simplifyArithmetic(createAnd(path.map(_.toExpr))))
    scala.io.StdIn.readLine()*/
    path
  }

  /**
   * 'neweexpr' is required to be in negation normal form and And/Ors have been pulled up
   */
  def conjoinWithDisjunct(guard: Variable, newexpr: Expr, callParents: List[FunDef], inSpec:Boolean) = {
     val (exprRoot, newGuards) = addConstraints(newexpr, callParents, _ => inSpec)
     //add 'newguard' in conjunction with 'disjuncts(guard)'
     val ctrs = disjuncts(guard)
     disjuncts -= guard
     disjuncts += (guard -> (BoolConstraint(exprRoot) +: ctrs))
     exprRoot
  }

  def conjoinWithRoot(newexpr: Expr, callParents: List[FunDef], inSpec: Boolean) = {
    val (exprRoot, newGuards) = addConstraints(newexpr, callParents, _ => inSpec)
    roots :+= exprRoot
    exprRoot
  }

  def getCallsOfGuards(guards: Seq[Variable]): Seq[Call] = {
    def calls(ctrs: Seq[Constraint]): Seq[Call] = {
      ctrs.flatMap {
        case c: Call => Seq(c)
        case ITE(_, th, el) =>
          calls(th) ++ calls(el)
        case _ => Seq()
      }
    }
    guards.flatMap{g => calls(disjuncts(g)) }
  }

  def callsInFormula: Seq[Call] = getCallsOfGuards(disjuncts.keys.toSeq)

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
    // simplify blockers if we can, and close the map
    val blockMap = substClosure(disjuncts.collect {
      case (g, Seq(ctr)) if !paramBlockers(g) => (g.id -> ctr.toExpr)
      case (g, Seq())                         => (g.id -> tru)
    }.toMap)
    val conjs = conjuncts.map {
      case (g, rhs) => replaceFromIDs(blockMap, combiningOp(g, rhs))
    }.toSeq ++ roots.map(replaceFromIDs(blockMap, _))
    val flatRest = disjuncts.toSeq collect {
      case (g, ctrs) if !paramBlockers(g) && !blockMap.contains(g.id) =>
        //val ng = blockMap.getOrElse(g.id, g)
        (g, replaceFromIDs(blockMap, createAnd(ctrs.map(_.toExpr))))
    }
    // compute variables used in more than one disjunct
    var sharedVars = (paramPart ++ conjs).flatMap(variablesOf).toSet
    var uniqueVars = Set[Identifier]()
    var freevars = Set[Identifier]()
    flatRest.foreach{
      case (g, rhs) =>
        val fvs = variablesOf(rhs).toSet
        val candUniques = fvs -- sharedVars
        val newShared = uniqueVars.intersect(candUniques)
        freevars ++= fvs
        sharedVars ++= newShared
        uniqueVars = (uniqueVars ++ candUniques) -- newShared
    }
    // unflatten rest
    var flatIdMap = blockMap
    val unflatRest = (flatRest collect {
      case (g, rhs) =>
        // note: we call simple unflatten in the presence of if-then-else because it will not have flat-ids transcending then and else branches
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

    if (dumpUnflatFormula) {
      val unf = ((paramPart ++ unflatRest.map(_.toString) ++ conjs.map(_.toString)).mkString("\n"))
      val filename = "unflatVC-" + FileCountGUID.getID
      val wr = new PrintWriter(new File(filename + ".txt"))
      println("Printed VC of " + fd.id + " to file: " + filename)
      wr.println(unf)
      wr.close()
    }
    if (ctx.dumpStats) {
      Stats.updateCounterStats(atomNum(And(paramPart ++ unflatRest ++ conjs)), "unflatSize", "VC-refinement")
    }
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
  def funsCount = disjuncts.map(_._2.count {
    case _: Call | _: ADTConstraint => true
    case _ => false
  }).sum

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
        Some(pickSatDisjunct(firstRoot, new SimpleLazyModel(unflatModel),
            tempMap.map{ case (Variable(id), v) => id -> v }.toMap, eval))
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

  /**
   * A method for picking a sat disjunct of unflat formula. Mostly used for debugging.
   */
  def pickSatFromUnflatFormula(unflate: Expr, model: Model, evaluator: DefaultEvaluator): Seq[Expr] = {
    def rec(e: Expr): Seq[Expr] = e match {
      case IfExpr(cond, thn, elze) =>
        (evaluator.eval(cond, model): @unchecked) match {
          case Successful(BooleanLiteral(true)) => cond +: rec(thn)
          case Successful(BooleanLiteral(false)) => Not(cond) +: rec(elze)
        }
      case And(args) => args flatMap rec
      case Or(args) => rec(args.find(evaluator.eval(_, model) == Successful(BooleanLiteral(true))).get)
      case Equals(b: Variable, rhs) if b.getType == BooleanType =>
        (evaluator.eval(b, model): @unchecked) match {
          case Successful(BooleanLiteral(true)) =>
            rec(b) ++ rec(rhs)
          case Successful(BooleanLiteral(false)) =>
            Seq(Not(b))
        }
      case e => Seq(e)
    }
    rec(unflate)
  }
}
