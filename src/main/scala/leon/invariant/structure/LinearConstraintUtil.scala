package leon
package invariant.structure

import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import java.io._
import invariant.util._
import BigInt._
import Constructors._

class NotImplementedException(message: String) extends RuntimeException(message) {

}

//a collections of utility methods that manipulate the templates
object LinearConstraintUtil {
  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val mone = InfiniteIntegerLiteral(-1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)

  //some utility methods
  def getFIs(ctr: LinearConstraint): Set[FunctionInvocation] = {
    val fis = ctr.coeffMap.keys.collect((e) => e match {
      case fi: FunctionInvocation => fi
    })
    fis.toSet
  }

  def evaluate(lt: LinearTemplate): Option[Boolean] = lt match {
    case lc: LinearConstraint if (lc.coeffMap.size == 0) =>
      ExpressionTransformer.simplify(lt.toExpr) match {
        case BooleanLiteral(v) => Some(v)
        case _ => None
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

    //println("Expr: "+expr)
    //these are the result values
    var coeffMap = MutableMap[Expr, Expr]()
    var constant: Option[Expr] = None
    var isTemplate : Boolean = false

    def addCoefficient(term: Expr, coeff: Expr) = {
      if (coeffMap.contains(term)) {
        val value = coeffMap(term)
        val newcoeff = simplifyArithmetic(Plus(value, coeff))

        //if newcoeff becomes zero remove it from the coeffMap
        if(newcoeff == zero) {
          coeffMap.remove(term)
        } else{
          coeffMap.update(term, newcoeff)
        }
      } else coeffMap += (term -> simplifyArithmetic(coeff))

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }

    def addConstant(coeff: Expr) ={
      if (constant.isDefined) {
        val value = constant.get
        constant = Some(simplifyArithmetic(Plus(value, coeff)))
      } else
        constant = Some(simplifyArithmetic(coeff))

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }

    //recurse into plus and get all minterms
    def getMinTerms(lexpr: Expr): Seq[Expr] = lexpr match {
      case Plus(e1, e2) => getMinTerms(e1) ++ getMinTerms(e2)
      case _ => Seq(lexpr)
    }

    val linearExpr = MakeLinear(expr)
    //the top most operator should be a relation
    val Operator(Seq(lhs, InfiniteIntegerLiteral(x)), op) = linearExpr
    /*if (lhs.isInstanceOf[InfiniteIntegerLiteral])
      throw new IllegalStateException("relation on two integers, not in canonical form: " + linearExpr)*/

    val minterms =  getMinTerms(lhs)

    //handle each minterm
    minterms.foreach((minterm: Expr) => minterm match {
      case _ if (Util.isTemplateExpr(minterm)) => {
        addConstant(minterm)
      }
      case Times(e1, e2) => {
        e2 match {
          case Variable(_) => ;
          case ResultVariable(_) => ;
          case FunctionInvocation(_, _) => ;
          case _ => throw new IllegalStateException("Multiplicand not a constraint variable: " + e2)
        }
        e1 match {
          //case c @ InfiniteIntegerLiteral(_) => addCoefficient(e2, c)
          case _ if (Util.isTemplateExpr(e1)) => {
            addCoefficient(e2, e1)
          }
          case _ => throw new IllegalStateException("Coefficient not a constant or template expression: " + e1)
        }
      }
      case Variable(_) => {
        //here the coefficient is 1
        addCoefficient(minterm, one)
      }
      case ResultVariable(_) => {
        addCoefficient(minterm, one)
      }
      case _ => throw new IllegalStateException("Unhandled min term: " + minterm)
    })

    if(coeffMap.isEmpty && constant.isEmpty) {
      //here the generated template the constant term is zero.
      new LinearConstraint(op, Map.empty, Some(zero))
    } else if(isTemplate) {
      new LinearTemplate(op, coeffMap.toMap, constant)
    } else{
      new LinearConstraint(op, coeffMap.toMap,constant)
    }
  }

  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints.
   * This assumes that the input expression is an atomic predicate (i.e, without and, or and nots)
   * This is subjected to constant modification.
   */
  def MakeLinear(atom: Expr): Expr = {

    //pushes the minus inside the arithmetic terms
    //we assume that inExpr is in linear form
    def PushMinus(inExpr: Expr): Expr = {
      inExpr match {
        case IntLiteral(v) => IntLiteral(-v)
        case InfiniteIntegerLiteral(v) => InfiniteIntegerLiteral(-v)
        case t: Terminal => Times(mone, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mone, fi)
        case UMinus(e1) => e1
        case RealUMinus(e1) => e1
        case Minus(e1, e2) => Plus(PushMinus(e1), e2)
        case RealMinus(e1, e2) => Plus(PushMinus(e1), e2)
        case Plus(e1, e2) => Plus(PushMinus(e1), PushMinus(e2))
        case RealPlus(e1, e2) => Plus(PushMinus(e1), PushMinus(e2))
        case Times(e1, e2) => {
          //here push the minus in to the coefficient which is the first argument
          Times(PushMinus(e1), e2)
        }
        case RealTimes(e1, e2) => Times(PushMinus(e1), e2)
        case _ => throw new NotImplementedException("PushMinus -- Operators not yet handled: " + inExpr)
      }
    }

    //we assume that ine is in linear form
    def PushTimes(mul: Expr, ine: Expr): Expr = {
      ine match {
        case t: Terminal => Times(mul, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mul, fi)
        case Plus(e1, e2) => Plus(PushTimes(mul, e1), PushTimes(mul, e2))
        case RealPlus(e1, e2) => Plus(PushTimes(mul, e1), PushTimes(mul, e2))
        case Times(e1, e2) => {
          //here push the times into the coefficient which should be the first expression
          Times(PushTimes(mul, e1), e2)
        }
        case RealTimes(e1, e2) => Times(PushTimes(mul, e1), e2)
        case _ => throw new NotImplementedException("PushTimes -- Operators not yet handled: " + ine)
      }
    }

    //collect all the constants in addition and simplify them
    //we assume that ine is in linear form and also that all constants are integers
    def simplifyConsts(ine: Expr): (Option[Expr], BigInt) = {
      ine match {
        case IntLiteral(v) => (None, v)
        case InfiniteIntegerLiteral(v) => (None, v)
        case Plus(e1, e2) => {
          val (r1, c1) = simplifyConsts(e1)
          val (r2, c2) = simplifyConsts(e2)

          val newe = (r1, r2) match {
            case (None, None) => None
            case (Some(t), None) => Some(t)
            case (None, Some(t)) => Some(t)
            case (Some(t1), Some(t2)) => Some(Plus(t1, t2))
          }
          (newe, c1 + c2)
        }
        case _ => (Some(ine), 0)
      }
    }

    def mkLinearRecur(inExpr: Expr): Expr = {
      inExpr match {
        case e @ Operator(Seq(e1, e2), op)
        if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
            || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
            || e.isInstanceOf[GreaterEquals])) => {

          //check if the expression has real valued sub-expressions
          val isReal = Util.hasReals(e1) || Util.hasReals(e2)
          //doing something else ... ?
    		  // println("[DEBUG] Expr 1 " + e1 + " of type " + e1.getType + " and Expr 2 " + e2 + " of type" + e2.getType)
          val (newe, newop) = e match {
            case t: Equals => (Minus(e1, e2), Equals)
            case t: LessEquals => (Minus(e1, e2), LessEquals)
            case t: GreaterEquals => (Minus(e2, e1), LessEquals)
            case t: LessThan => {
              if (isReal)
                (Minus(e1, e2), LessThan)
              else
                (Plus(Minus(e1, e2), one), LessEquals)
            }
            case t: GreaterThan => {
              if(isReal)
                 (Minus(e2,e1),LessThan)
              else
            	 (Plus(Minus(e2, e1), one), LessEquals)
            }
          }
          val r = mkLinearRecur(newe)
          //simplify the resulting constants
          val (r2, const) = simplifyConsts(r)
          val finale = if (r2.isDefined) {
            if (const != 0) Plus(r2.get, InfiniteIntegerLiteral(const))
            else r2.get
          } else InfiniteIntegerLiteral(const)
          //println(r + " simplifies to "+finale)
          newop(finale, zero)
        }
        case Minus(e1, e2) => Plus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case RealMinus(e1, e2) => RealPlus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case RealUMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(_, _) | RealTimes(_, _) => {
          val Operator(Seq(e1, e2), op) = inExpr
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          if(Util.isTemplateExpr(r1)) {
            PushTimes(r1, r2)
          } else if(Util.isTemplateExpr(r2)){
            PushTimes(r2, r1)
          } else
            throw new IllegalStateException("Expression not linear: " + Times(r1, r2))
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case RealPlus(e1, e2) => RealPlus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal => t
        case fi: FunctionInvocation => fi
        case _ => throw new IllegalStateException("Expression not linear: " + inExpr)
      }
    }
    val rese = mkLinearRecur(atom)
    rese
  }

  /**
   * Replaces an expression by another expression in the terms of the given linear constraint.
   */
  def replaceInCtr(replaceMap: Map[Expr, Expr], lc: LinearConstraint): Option[LinearConstraint] = {

    //println("Replacing in "+lc+" repMap: "+replaceMap)
    val newexpr = ExpressionTransformer.simplify(simplifyArithmetic(replace(replaceMap, lc.toExpr)))
    //println("new expression: "+newexpr)
    if (newexpr == tru) None
    else if(newexpr == fls) throw new IllegalStateException("!!Constraint reduced to false during elimination: " + lc)
    else {
      val res = exprToTemplate(newexpr)
      //check if res is true or false
      evaluate(res) match {
        case Some(false) => throw new IllegalStateException("!!Constraint reduced to false during elimination: " + lc)
        case Some(true) => None //constraint reduced to true
        case _ =>
          val resctr = res.asInstanceOf[LinearConstraint]
          Some(resctr)
      }
    }
  }

    /**
   * Eliminates the specified variables from a conjunction of linear constraints (a disjunct) (that is satisfiable)
   * We assume that the disjunct is in nnf form
   *
   * debugger is a function used for debugging
   */
  val debugElimination = false
  def apply1PRuleOnDisjunct(linearCtrs: Seq[LinearConstraint], elimVars: Set[Identifier],
      debugger: Option[(Seq[LinearConstraint] => Unit)]): Seq[LinearConstraint] = {
    //eliminate one variable at a time
    //each iteration produces a new set of linear constraints
    elimVars.foldLeft(linearCtrs)((acc, elimVar) => {
      val newdisj = apply1PRuleOnDisjunct(acc, elimVar)

      if(debugElimination) {
        if(debugger.isDefined) {
          debugger.get(newdisj)
        }
      }

      newdisj
    })
  }

  def apply1PRuleOnDisjunct(linearCtrs: Seq[LinearConstraint], elimVar: Identifier): Seq[LinearConstraint] = {

    if(debugElimination)
      println("Trying to eliminate: "+elimVar)

    //collect all relevant constraints
    val emptySeq = Seq[LinearConstraint]()
    val (relCtrs, rest) = linearCtrs.foldLeft((emptySeq,emptySeq))((acc,lc) => {
      if(variablesOf(lc.toExpr).contains(elimVar)) {
        (lc +: acc._1,acc._2)
      } else {
        (acc._1,lc +: acc._2)
      }
    })

    //now consider each constraint look for (a) equality involving the elimVar or (b) check if all bounds are lower
    //or (c) if all bounds are upper.
    var elimExpr : Option[Expr] = None
    var bestExpr = false
    var elimCtr : Option[LinearConstraint] = None
    var allUpperBounds : Boolean = true
    var allLowerBounds : Boolean = true
    var foundEquality : Boolean = false
    var skippingEquality : Boolean = false

    relCtrs.foreach((lc) => {
      //check for an equality
      if (lc.toExpr.isInstanceOf[Equals] && lc.coeffMap.contains(elimVar.toVariable)) {
        foundEquality = true

        //here, sometimes we replace an existing expression with a better one if available
        if (!elimExpr.isDefined || shouldReplace(elimExpr.get, lc, elimVar)) {
          //if the coeffcient of elimVar is +ve the the sign of the coeff of every other term should be changed
          val InfiniteIntegerLiteral(elimCoeff) = lc.coeffMap(elimVar.toVariable)
          //make sure the value of the coefficient is 1 or  -1
          //TODO: handle cases wherein the coefficient is not 1 or -1
          if (elimCoeff == 1 || elimCoeff == -1) {
            val changeSign = if (elimCoeff > 0) true else false

            val startval = if (lc.const.isDefined) {
              val InfiniteIntegerLiteral(cval) = lc.const.get
              val newconst = if (changeSign) -cval else cval
              InfiniteIntegerLiteral(newconst)

            } else zero

            val substExpr = lc.coeffMap.foldLeft(startval: Expr)((acc, summand) => {
              val (term, InfiniteIntegerLiteral(coeff)) = summand
              if (term != elimVar.toVariable) {

                val newcoeff = if (changeSign) -coeff else coeff
                val newsummand = if (newcoeff == 1) term else Times(term, InfiniteIntegerLiteral(newcoeff))
                if (acc == zero) newsummand
                else Plus(acc, newsummand)

              } else acc
            })

            elimExpr = Some(simplifyArithmetic(substExpr))
            elimCtr = Some(lc)

            if (debugElimination) {
              println("Using ctr: " + lc + " found mapping: " + elimVar + " --> " + substExpr)
            }
          } else {
            skippingEquality = true
          }
        }
      } else if ((lc.toExpr.isInstanceOf[LessEquals] || lc.toExpr.isInstanceOf[LessThan])
        && lc.coeffMap.contains(elimVar.toVariable)) {

        val InfiniteIntegerLiteral(elimCoeff) = lc.coeffMap(elimVar.toVariable)
        if (elimCoeff > 0) {
          //here, we have found an upper bound
          allLowerBounds = false
        } else {
          //here, we have found a lower bound
          allUpperBounds = false
        }
      } else {
        //here, we assume that the operators are normalized to Equals, LessThan and LessEquals
        throw new IllegalStateException("LinearConstraint not in expeceted form : " + lc.toExpr)
      }
    })

    val newctrs = if (elimExpr.isDefined) {

      val elimMap = Map[Expr, Expr](elimVar.toVariable -> elimExpr.get)
      var repCtrs = Seq[LinearConstraint]()
      relCtrs.foreach((ctr) => {
        if (ctr != elimCtr.get) {
          //replace 'elimVar' by 'elimExpr' in ctr
          val repCtr = this.replaceInCtr(elimMap, ctr)
          if (repCtr.isDefined)
            repCtrs +:= repCtr.get
        }
      })
      repCtrs

    } else if (!foundEquality && (allLowerBounds || allUpperBounds)) {
      //here, drop all relCtrs. None of them are important
      Seq()
    } else {
      //for stats
      if(skippingEquality) {
        Stats.updateCumStats(1,"SkippedVar")
      }
      //cannot eliminate the variable
      relCtrs
    }
    val resctrs = (newctrs ++ rest)
    //println("After eliminating: "+elimVar+" : "+resctrs)
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

  def sizeCtr(ctr : LinearConstraint) : Int = {
    val coeffSize = ctr.coeffMap.foldLeft(0)((acc, pair) => {
      val (term, coeff) = pair
      if(coeff == one) acc + 1
      else acc + sizeExpr(coeff) + 2
    })
    if(ctr.const.isDefined) coeffSize + 1
    else coeffSize
  }

  def shouldReplace(currExpr : Expr, candidateCtr : LinearConstraint, elimVar: Identifier) : Boolean = {
    if(!currExpr.isInstanceOf[InfiniteIntegerLiteral]) {
      //is the candidate a constant
      if(candidateCtr.coeffMap.size == 1) true
      else{
        //computing the size of currExpr
        if(sizeExpr(currExpr) > (sizeCtr(candidateCtr) - 1)) true
        else false
      }
    } else false
  }

  //remove transitive axioms

  /**
   * Checks if the expression is linear i.e,
   * is only conjuntion and disjunction of linear atomic predicates
   */
  def isLinear(e: Expr) : Boolean = {
     e match {
       case And(args) => args forall isLinear
       case Or(args) => args forall isLinear
       case Not(arg) => isLinear(arg)
       case Implies(e1, e2) => isLinear(e1) && isLinear(e2)
       case t : Terminal => true
       case atom =>
         exprToTemplate(atom).isInstanceOf[LinearConstraint]
     }
  }
}

