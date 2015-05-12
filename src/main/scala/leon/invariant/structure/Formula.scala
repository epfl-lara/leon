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

/**
 * Data associated with a call
 */
class CallData(val guard : Variable, val parents: List[FunDef]) {
}

/**
 * Representation of an expression as a set of implications.
 * 'initexpr' is required to be in negation normal form and And/Ors have been pulled up
 * TODO: optimize the representation so that we use fewer guards.
 */
class Formula(val fd: FunDef, initexpr: Expr, ctx: InferenceContext) {

  val fls = BooleanLiteral(false)
  val tru = BooleanLiteral(true)
  val useImplies = false

  val combiningOp = if(useImplies) Implies.apply _ else Equals.apply _
  protected var disjuncts = Map[Variable, Seq[Constraint]]() //a mapping from guards to conjunction of atoms
  protected var conjuncts = Map[Variable, Expr]() //a mapping from guards to disjunction of atoms
  private var callDataMap = Map[Call, CallData]() //a mapping from a 'call' to the 'guard' guarding the call plus the list of transitive callers of 'call'

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

    val f1 = simplePostTransform((e: Expr) => e match {
      case Or(args) => {
        val newargs = args.map(arg => arg match {
          case v: Variable if (disjuncts.contains(v)) => arg
          case v: Variable if (conjuncts.contains(v)) => throw new IllegalStateException("or gaurd inside conjunct: "+e+" or-guard: "+v)
          case _ => {
            val atoms = arg  match {
              case And(atms) => atms
              case _ => Seq(arg)
            }
            val g = TVarFactory.createTemp("b", BooleanType).toVariable
            newDisjGuards :+= g
            //println("atoms: "+atoms)
            val ctrs = getCtrsFromExprs(g, atoms)
            disjuncts += (g -> ctrs)
            g
          }
        })
        //create a temporary for Or
        val gor = TVarFactory.createTemp("b", BooleanType).toVariable
        val newor = Util.createOr(newargs)
        conjuncts += (gor -> newor)
        gor
      }
      case And(args) => {
        val newargs = args.map(arg => if (Util.getTemplateVars(e).isEmpty) {
          arg
        } else {
          //if the expression has template variables then we separate it using guards
          val g = TVarFactory.createTemp("b", BooleanType).toVariable
          newDisjGuards :+= g
          val ctrs = getCtrsFromExprs(g, Seq(arg))
          disjuncts += (g -> ctrs)
          g
        })
        Util.createAnd(newargs)
      }
      case _ => e
    })(ExpressionTransformer.simplify(simplifyArithmetic(
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
        val g = TVarFactory.createTemp("b", BooleanType).toVariable
        val ctrs = getCtrsFromExprs(g, atoms)
        newDisjGuards :+= g
        disjuncts += (g -> ctrs)
        g
      }
    }
    (rootvar, newDisjGuards)
  }

  //'satGuard' is required to a guard variable
  def pickSatDisjunct(startGaurd : Variable, model: Model): Seq[Constraint] = {

    def traverseOrs(gd: Variable, model: Model): Seq[Variable] = {
      val e @ Or(guards) = conjuncts(gd)
      //pick one guard that is true
      val guard = guards.collectFirst { case g @ Variable(id) if (model(id) == tru) => g }
      if (!guard.isDefined)
        throw new IllegalStateException("No satisfiable guard found: " + e)
      guard.get +: traverseAnds(guard.get, model)
    }

    def traverseAnds(gd: Variable, model: Model): Seq[Variable] = {
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

  /**
   * The first return value is param part and the second one is the
   * non-parametric part
   */
  def splitParamPart : (Expr, Expr) = {
    var paramPart = Seq[Expr]()
    var rest = Seq[Expr]()
    disjuncts.foreach(entry => {
      val (g,ctrs) = entry
      val ctrExpr = combiningOp(g,Util.createAnd(ctrs.map(_.toExpr)))
      if(Util.getTemplateVars(ctrExpr).isEmpty)
        rest :+= ctrExpr
      else
        paramPart :+= ctrExpr

    })
    val conjs = conjuncts.map((entry) => combiningOp(entry._1, entry._2)).toSeq ++ roots
    (Util.createAnd(paramPart), Util.createAnd(rest ++ conjs ++ roots))
  }

  def toExpr : Expr={
    val disjs = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      combiningOp(g, Util.createAnd(ctrs.map(_.toExpr)))
    }).toSeq
    val conjs = conjuncts.map((entry) => combiningOp(entry._1, entry._2)).toSeq
    Util.createAnd(disjs ++ conjs ++ roots)
  }

  //unpack the disjunct and conjuncts by removing all guards
  def unpackedExpr : Expr = {
    //replace all conjunct guards in disjuncts by their mapping
    val disjs : Map[Expr,Expr] = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      val newctrs = ctrs.map(_ match {
        case BoolConstraint(g@Variable(_)) if conjuncts.contains(g) => conjuncts(g)
        case ctr@_ => ctr.toExpr
      })
      (g, Util.createAnd(newctrs))
    })
    val rootexprs = roots.map(_ match {
        case g@Variable(_) if conjuncts.contains(g) => conjuncts(g)
        case e@_ => e
      })
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
          /*println("Disunct: "+d)
          println("guard replaced: "+guards)*/
          replacedGuard = true
          //removeGuards ++= guards
          (g, replace(unpackedDisjs, d))
        }
      })
      unpackedDisjs = newDisjs
    }
    //replace all the 'guards' in root using 'unpackedDisjs'
    replace(unpackedDisjs, Util.createAnd(rootexprs))
  }

  override def toString : String = {
    val disjStrs = disjuncts.map((entry) => {
      val (g,ctrs) = entry
      simplifyArithmetic(combiningOp(g, Util.createAnd(ctrs.map(_.toExpr)))).toString
    }).toSeq
    val conjStrs = conjuncts.map((entry) => combiningOp(entry._1, entry._2).toString).toSeq
    val rootStrs = roots.map(_.toString)
    (disjStrs ++ conjStrs ++ rootStrs).foldLeft("")((acc,str) => acc + "\n" + str)
  }
}
