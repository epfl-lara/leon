/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.structure

import purescala._
import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import leon.purescala.Types._
import purescala.Extractors._
import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet, MutableList }
import invariant.util._
import BigInt._
import PredicateUtil._
import Stats._

class NotImplementedException(message: String) extends RuntimeException(message)

//a collections of utility methods that manipulate the templates
object LinearConstraintUtil {
  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val mone = InfiniteIntegerLiteral(-1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)

  val debugElimination = false

  //some utility methods
  def getFIs(ctr: LinearConstraint): Set[FunctionInvocation] = {
    val fis = ctr.coeffMap.keys.collect {
      case fi: FunctionInvocation => fi
    }
    fis.toSet
  }

  def evaluate(lt: LinearTemplate): Option[Boolean] = lt match {
    case lc: LinearConstraint if lc.coeffMap.isEmpty =>
      ExpressionTransformer.simplify(lt.toExpr) match {
        case BooleanLiteral(v) => Some(v)
        case _                 => None
      }
    case _ => None
  }

  /**
   * the expression 'Expr' is required to be a linear atomic predicate (or a template),
   * if not, an exception would be thrown.
   * For now some of the constructs are not handled.
   * The function returns a linear template or a linear constraint depending
   * on whether the expression has template variables or not
   */
  def exprToTemplate(expr: Expr): LinearTemplate = {

    //these are the result values
    var coeffMap = MutableMap[Expr, Expr]()
    var constant: Option[Expr] = None
    var isTemplate: Boolean = false

    def addCoefficient(term: Expr, coeff: Expr) = {
      if (coeffMap.contains(term)) {
        val value = coeffMap(term)
        val newcoeff = simplifyArithmetic(Plus(value, coeff))
        //if newcoeff becomes zero remove it from the coeffMap
        if (newcoeff == zero) {
          coeffMap.remove(term)
        } else {
          coeffMap.update(term, newcoeff)
        }
      } else coeffMap += (term -> simplifyArithmetic(coeff))
      if (variablesOf(coeff).nonEmpty) {
        isTemplate = true
      }
    }

    def addConstant(coeff: Expr) = {
      if (constant.isDefined) {
        val value = constant.get
        constant = Some(simplifyArithmetic(Plus(value, coeff)))
      } else
        constant = Some(simplifyArithmetic(coeff))
      if (variablesOf(coeff).nonEmpty) {
        isTemplate = true
      }
    }

    //recurse into plus and get all minterms
    def getMinTerms(lexpr: Expr): Seq[Expr] = lexpr match {
      case Plus(e1, e2) => getMinTerms(e1) ++ getMinTerms(e2)
      case _            => Seq(lexpr)
    }

    //the top most operator should be a relation
    val Operator(Seq(lhs, InfiniteIntegerLiteral(x)), op) = makeLinear(expr)
    /*if (lhs.isInstanceOf[InfiniteIntegerLiteral])
      throw new IllegalStateException("relation on two integers, not in canonical form: " + linearExpr)*/
    //handle each minterm
    getMinTerms(lhs).foreach(minterm => minterm match {
      case _ if (isTemplateExpr(minterm)) => addConstant(minterm)
      case Times(e1, e2) =>
        e2 match {
          case Variable(_) | ResultVariable(_) | FunctionInvocation(_, _) =>
          case _                        => throw new IllegalStateException("Multiplicand not a constraint variable: " + e2)
        }
        e1 match {
          case _ if (isTemplateExpr(e1)) => addCoefficient(e2, e1)
          case _ => throw new IllegalStateException("Coefficient not a constant or template expression: " + e1)
        }
      case Variable(_) => addCoefficient(minterm, one) //here the coefficient is 1
      case ResultVariable(_) => addCoefficient(minterm, one)
      case _ => throw new IllegalStateException("Unhandled min term: " + minterm)
    })

    if (coeffMap.isEmpty && constant.isEmpty) {
      //here the generated template the constant term is zero.
      new LinearConstraint(op, Map.empty, Some(zero))
    } else if (isTemplate) {
      new LinearTemplate(op, coeffMap.toMap, constant)
    } else {
      new LinearConstraint(op, coeffMap.toMap, constant)
    }
  }

  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints.
   * This assumes that the input expression is an atomic predicate (i.e, without and, or and nots)
   * This is subjected to constant modification.
   */
  def makeLinear(atom: Expr): Expr = {

    //pushes the minus inside the arithmetic terms
    //we assume that inExpr is in linear form
    def pushMinus(inExpr: Expr): Expr = {
      inExpr match {
        case IntLiteral(v)                       => IntLiteral(-v)
        case InfiniteIntegerLiteral(v)           => InfiniteIntegerLiteral(-v)
        case t: Terminal                         => Times(mone, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mone, fi)
        case UMinus(e1)                          => e1
        case RealUMinus(e1)                      => e1
        case Minus(e1, e2)                       => Plus(pushMinus(e1), e2)
        case RealMinus(e1, e2)                   => Plus(pushMinus(e1), e2)
        case Plus(e1, e2)                        => Plus(pushMinus(e1), pushMinus(e2))
        case RealPlus(e1, e2)                    => Plus(pushMinus(e1), pushMinus(e2))
        case Times(e1, e2) =>
          //here push the minus in to the coefficient which is the first argument
          Times(pushMinus(e1), e2)
        case RealTimes(e1, e2) => Times(pushMinus(e1), e2)
        case _                 => throw new NotImplementedException("pushMinus -- Operators not yet handled: " + inExpr)
      }
    }

    //we assume that ine is in linear form
    def pushTimes(mul: Expr, ine: Expr): Expr = {
      val isReal = ine.getType == RealType && mul.getType == RealType
      val timesCons =
        if (isReal) RealTimes
        else Times
      ine match {
        case t: Terminal                        => timesCons(mul, t)
        case fi @ FunctionInvocation(fdef, ars) => timesCons(mul, fi)
        case Plus(e1, e2)                       => Plus(pushTimes(mul, e1), pushTimes(mul, e2))
        case RealPlus(e1, e2) =>
          val r1 = pushTimes(mul, e1)
          val r2 = pushTimes(mul, e2)
          if (isReal) RealPlus(r1, r2)
          else Plus(r1, r2)
        case Times(e1, e2) =>
          //here push the times into the coefficient which should be the first expression
          Times(pushTimes(mul, e1), e2)
        case RealTimes(e1, e2) =>
          val r = pushTimes(mul, e1)
          if (isReal) RealTimes(r, e2)
          else Times(r, e2)
        case _ => throw new NotImplementedException("pushTimes -- Operators not yet handled: " + ine)
      }
    }

    //collect all the constants in addition and simplify them
    //we assume that ine is in linear form and also that all constants are integers
    def simplifyConsts(ine: Expr): (Option[Expr], BigInt) = {
      ine match {
        case IntLiteral(v)             => (None, v)
        case InfiniteIntegerLiteral(v) => (None, v)
        case Plus(e1, e2) => {
          val (r1, c1) = simplifyConsts(e1)
          val (r2, c2) = simplifyConsts(e2)
          val newe = (r1, r2) match {
            case (None, None)         => None
            case (Some(t), None)      => Some(t)
            case (None, Some(t))      => Some(t)
            case (Some(t1), Some(t2)) => Some(Plus(t1, t2))
          }
          (newe, c1 + c2)
        }
        case _ => (Some(ine), 0)
      }
    }

    def mkLinearRecur(inExpr: Expr): Expr = {
      //println("inExpr: "+inExpr + " tpe: "+inExpr.getType)
      val res = inExpr match {
        case e @ Operator(Seq(e1, e2), op) if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
          || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
          || e.isInstanceOf[GreaterEquals])) => {

          //check if the expression has real valued sub-expressions
          val isReal = hasRealsOrTemplates(e1) || hasRealsOrTemplates(e2)
          val (newe, newop) = e match {
            case t: Equals        => (Minus(e1, e2), Equals)
            case t: LessEquals    => (Minus(e1, e2), LessEquals)
            case t: GreaterEquals => (Minus(e2, e1), LessEquals)
            case t: LessThan =>
              if (isReal)
                (Minus(e1, e2), LessThan)
              else
                (Plus(Minus(e1, e2), one), LessEquals)
            case t: GreaterThan =>
              if (isReal)
                (Minus(e2, e1), LessThan)
              else
                (Plus(Minus(e2, e1), one), LessEquals)
          }
          val r = mkLinearRecur(newe)
          //simplify the resulting constants
          val (r2, const) = simplifyConsts(r)
          val finale = if (r2.isDefined) {
            if (const != 0) Plus(r2.get, InfiniteIntegerLiteral(const))
            else r2.get
          } else InfiniteIntegerLiteral(const)
          newop(finale, zero)
        }
        case Minus(e1, e2)     => Plus(mkLinearRecur(e1), pushMinus(mkLinearRecur(e2)))
        case RealMinus(e1, e2) => RealPlus(mkLinearRecur(e1), pushMinus(mkLinearRecur(e2)))
        case UMinus(e1)        => pushMinus(mkLinearRecur(e1))
        case RealUMinus(e1)    => pushMinus(mkLinearRecur(e1))
        case Times(_, _) | RealTimes(_, _) => {
          val Operator(Seq(e1, e2), op) = inExpr
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          if (isTemplateExpr(r1))
            pushTimes(r1, r2)
          else if (isTemplateExpr(r2))
            pushTimes(r2, r1)
          else
            throw new IllegalStateException("Expression not linear: " + Times(r1, r2))
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case rp @ RealPlus(e1, e2) =>
          RealPlus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal            => t
        case fi: FunctionInvocation => fi
        case _                      => throw new IllegalStateException("Expression not linear: " + inExpr)
      }
      res
    }
    val rese = mkLinearRecur(atom)
    rese
  }

  /**
   * Replaces an expression by another expression in the terms of the given linear constraint.
   */
  def replaceInCtr(replaceMap: Map[Identifier, Expr], lc: LinearConstraint): Option[LinearConstraint] = {
    //println("Replacing in "+lc+" repMap: "+replaceMap)
    val newexpr = ExpressionTransformer.simplify(replaceFromIDs(replaceMap, lc.toExpr))
    if (newexpr == tru) None
    else if (newexpr == fls) throw new IllegalStateException("!!Constraint reduced to false during elimination: " + lc)
    else {
      val res = exprToTemplate(newexpr)
      //check if res is true or false
      evaluate(res) match {
        case Some(false) => throw new IllegalStateException("!!Constraint reduced to false during elimination: " + lc)
        case Some(true)  => None //constraint reduced to true
        case _ =>
          Some(res.asInstanceOf[LinearConstraint])
      }
    }
  }

  def ctrVars(lc: LinearConstraint) = lc.coeffMap.keySet.map { case Variable(id) => id }

  /**
   * Eliminates all variables except the `retainVars` from a conjunction of linear constraints (a disjunct) (that is satisfiable)
   * We assume that the disjunct is in nnf form.
   * The strategy is to look for (a) equality involving the elimVars or (b) check if all bounds are lower or (c) if all bounds are upper.
   * TODO: handle cases wherein the coefficient of the variable that is substituted is not 1 or -1
   *
   * @param debugger is a function used for debugging
   */
  def apply1PRuleOnDisjunct(linearCtrs: Seq[LinearConstraint], retainVars: Set[Identifier],
                            debugger: Option[(Seq[LinearConstraint] => Unit)]): Seq[LinearConstraint] = {
    val idsWithUpperBounds = MutableSet[Identifier]() // identifiers with only upper bounds
    val idsWithLowerBounds = MutableSet[Identifier]() // identifiers with only lower bounds
    val idsWithEquality = MutableSet[Identifier]() // identifiers for which an equality constraint exist
    var eqctrs = MutableList[LinearConstraint]()
    var restctrs = MutableList[LinearConstraint]()
    linearCtrs.foreach {
      case lc =>
        val vars = ctrVars(lc)
        val elimVars = vars -- retainVars
        lc.template match {
          case eq: Equals =>
            idsWithEquality ++= vars
            if (!elimVars.isEmpty)
              eqctrs += lc
            else restctrs += lc
          // choose all vars whose coefficient is either 1 or -1
          case _: LessEquals | _: LessThan =>
            elimVars.foreach { elimVar =>
              val InfiniteIntegerLiteral(elimCoeff) = lc.coeffMap(elimVar.toVariable)
              if (elimCoeff > 0)
                idsWithUpperBounds += elimVar //here, we have found an upper bound
              else
                idsWithLowerBounds += elimVar //here, we have found a lower bound
            }
            restctrs += lc
          case _ => throw new IllegalStateException("LinearConstraint not in expeceted form : " + lc.toExpr)
        }
    }
    // sort 'eqctrs' by the size of the constraints so that we use smaller expressions in 'subst' map.
    var currEqs = eqctrs.sortBy(eqc => eqc.coeffMap.keySet.size + (if (eqc.const.isDefined) 1 else 0))
    // compute the subst map recursively
    var nextEqs = MutableList[LinearConstraint]()
    var foundSubst = true
    var subst = Map[Identifier, Expr]()
    while (foundSubst) {
      foundSubst = false
      currEqs.foreach { eq =>
        // replace the constraint by the current subst (which may require multiple applications)
        replaceInCtr(subst, eq) match {
          case None => // constraint reduced to true, drop the constraint
          case Some(newc) =>
            // choose one new variable that can be substituted
            val elimVarOpt = ctrVars(newc).find { evar =>
              !retainVars.contains(evar) && !subst.contains(evar) &&
                (newc.coeffMap(evar.toVariable) match {
                  case InfiniteIntegerLiteral(elimCoeff) if (elimCoeff == 1 || elimCoeff == -1) => true
                  case _ => false
                })
            }
            elimVarOpt match {
              case None =>
                nextEqs += newc // here, the constraint cannot be substituted, so we need to preserve it
              case Some(elimVar) =>
                //if the coeffcient of elimVar is +ve the the sign of the coeff of every other term should be changed
                val InfiniteIntegerLiteral(elimCoeff) = newc.coeffMap(elimVar.toVariable)
                val changeSign = elimCoeff > 0
                val startval = if (newc.const.isDefined) {
                  val InfiniteIntegerLiteral(cval) = newc.const.get
                  val newconst = if (changeSign) -cval else cval
                  InfiniteIntegerLiteral(newconst)
                } else zero
                val substExpr = newc.coeffMap.foldLeft(startval: Expr) {
                  case (acc, (term, InfiniteIntegerLiteral(coeff))) if (term != elimVar.toVariable) =>
                    val newcoeff = if (changeSign) -coeff else coeff
                    val newsummand = if (newcoeff == 1) term else Times(term, InfiniteIntegerLiteral(newcoeff))
                    if (acc == zero) newsummand
                    else Plus(acc, newsummand)
                  case (acc, _) => acc
                }
                if (debugElimination) {
                  println("Analyzing ctr: " + newc + " found mapping: " + elimVar + " --> " + substExpr)
                }
                subst = Util.substClosure(subst + (elimVar -> simplifyArithmetic(substExpr)))
                foundSubst = true
            }
        }
      }
      currEqs = nextEqs
    }
    val oneSidedVars = ((idsWithUpperBounds -- idsWithLowerBounds) ++ (idsWithLowerBounds -- idsWithUpperBounds)) -- idsWithEquality
    val resctrs = (restctrs.flatMap {
      case ctr if ctrVars(ctr).intersect(oneSidedVars).isEmpty =>
        replaceInCtr(subst, ctr) match {
          case None         => Seq()
          case Some(newctr) => Seq(newctr)
        }
      case _ => Seq() // drop constraints with `oneSidedVars`
    } ++ currEqs).distinct // note: this is very important!!
    Stats.updateCumStats(currEqs.size, "UneliminatedEqualities")
    resctrs
  }

  def sizeExpr(ine: Expr): Int = {
    val simpe = simplifyArithmetic(ine)
    var size = 0
    simplePostTransform((e: Expr) => {
      size += 1
      e
    })(simpe)
    size
  }

  def sizeCtr(ctr: LinearConstraint): Int = {
    val coeffSize = ctr.coeffMap.foldLeft(0)((acc, pair) => {
      val (term, coeff) = pair
      if (coeff == one) acc + 1
      else acc + sizeExpr(coeff) + 2
    })
    if (ctr.const.isDefined) coeffSize + 1
    else coeffSize
  }

  /**
   * Checks if the expression is linear i.e,
   * is only conjuntion and disjunction of linear atomic predicates
   */
  def isLinearFormula(e: Expr): Boolean = {
    e match {
      case And(args)       => args forall isLinearFormula
      case Or(args)        => args forall isLinearFormula
      case Not(arg)        => isLinearFormula(arg)
      case Implies(e1, e2) => isLinearFormula(e1) && isLinearFormula(e2)
      case t: Terminal     => true
      case atom =>
        exprToTemplate(atom).isInstanceOf[LinearConstraint]
    }
  }
}
