package leon
package invariant

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.ExtendedVC



//a collections of utility methods that manipulate the templates
object LinearConstraintUtil {
  val zero = IntLiteral(0)
  val one = IntLiteral(1)
  val mone = IntLiteral(-1)
  val tru = BooleanLiteral(true)
  
  def exprToTemplate(expr: Expr): LinearTemplate = {
    val res = tryExprToTemplate(expr)
    if(res.isDefined) res.get
    else throw new IllegalStateException("The expression reduced to True: "+expr)
  }
   /**
   * the expression 'Expr' is required to be a linear atomic predicate (or a template),
   * if not, an exception would be thrown.
   * For now some of the constructs are not handled.
   * The function returns a linear template or a linear constraint depending
   * on whether the expression has template variables or not
   */
  def tryExprToTemplate(expr: Expr): Option[LinearTemplate] = {
    
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
      } else coeffMap += (term -> coeff)

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }
    
    def addConstant(coeff: Expr) ={
      if (constant.isDefined) {
        val value = constant.get
        constant = Some(Plus(value, coeff))
      } else 
        constant = Some(coeff)

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }
   
    val linearExpr = MakeLinear(expr)

    //the top most operator should be a relation
    val BinaryOperator(lhs, IntLiteral(0), op) = linearExpr
    if (lhs.isInstanceOf[IntLiteral])
      throw IllegalStateException("relation on two integers, not in canonical form: " + linearExpr)

    //recurse into plus and get all minterms
    def getMinTerms(lexpr: Expr): Seq[Expr] = lexpr match {
      case Plus(e1, e2) => getMinTerms(e1) ++ getMinTerms(e2)      
      case _ => Seq(lexpr)
    }
    val minterms =  getMinTerms(lhs)

    //handle each minterm
    minterms.foreach((minterm: Expr) => minterm match {
      case _ if (InvariantUtil.isTemplateExpr(minterm)) => {
        addConstant(minterm)
      }
      case Times(e1, e2) => {
        e2 match {
          case Variable(_) => ;
          case ResultVariable() => ;
          case FunctionInvocation(_, _) => ;
          case _ => throw IllegalStateException("Multiplicand not a constraint variable: " + e2)
        }
        e1 match {
          //case c @ IntLiteral(_) => addCoefficient(e2, c)
          case _ if (InvariantUtil.isTemplateExpr(e1)) => {
            addCoefficient(e2, e1)            
          }
          case _ => throw IllegalStateException("Coefficient not a constant or template expression: " + e1)
        }
      }            
      case Variable(_) => {
        //here the coefficient is 1
        addCoefficient(minterm, one)
      }
      case ResultVariable() => {
        addCoefficient(minterm, one)
      }
      case _ => throw IllegalStateException("Unhandled min term: " + minterm)
    })
    
    if(coeffMap.isEmpty && constant.isEmpty) {
      //here the generated template reduced to true
      None
    } else if(isTemplate) {  
      Some(new LinearTemplate(op, coeffMap.toMap, constant))
    } else{
      Some(new LinearConstraint(op, coeffMap.toMap,constant))      
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
      require(inExpr.getType == Int32Type || inExpr.getType == RealType)

      inExpr match {
        case IntLiteral(v) => IntLiteral(-v)
        case t: Terminal => Times(mone, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mone, fi)
        case UMinus(e1) => e1
        case Minus(e1, e2) => Plus(PushMinus(e1), e2)
        case Plus(e1, e2) => Plus(PushMinus(e1), PushMinus(e2))
        case Times(e1, e2) => {
          //here push the minus in to the coefficient which is the first argument
          Times(PushMinus(e1), e2)          
        }
        case _ => throw NotImplementedException("PushMinus -- Operators not yet handled: " + inExpr)
      }
    }

    //we assume that ine is in linear form
    def PushTimes(mul: Expr, ine: Expr): Expr = {
      ine match {
        //case IntLiteral(v) => IntLiteral(c * v)
        case t: Terminal => Times(mul, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mul, fi)
        case Plus(e1, e2) => Plus(PushTimes(mul, e1), PushTimes(mul, e2))
        case Times(e1, e2) => {
          //here push the times into the coefficient which should be the first expression
          Times(PushTimes(mul, e1), e2)
        }
        case _ => throw NotImplementedException("PushTimes -- Operators not yet handled: " + ine)
      }
    }

    //collect all the constants in addition and simplify them
    //we assume that ine is in linear form
    def simplifyConsts(ine: Expr): (Option[Expr], Int) = {
      require(ine.getType == Int32Type || ine.getType == RealType)

      ine match {
        case IntLiteral(v) => (None, v)
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
        case e @ BinaryOperator(e1, e2, op) 
        if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
            || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
            || e.isInstanceOf[GreaterEquals])) => {

          //check if the expression has real valued sub-expressions
          val isReal = InvariantUtil.hasReals(e1) || InvariantUtil.hasReals(e2) 
          val (newe, newop) = e match {
            case t: Equals => (Minus(e1, e2), op)
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
          val (Some(r2), const) = simplifyConsts(r)
          val finale = if (const != 0) Plus(r2, IntLiteral(const)) else r2
          //println(r + " simplifies to "+finale)
          newop(finale, zero)
        }
        case Minus(e1, e2) => Plus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(e1, e2) => {
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          
          if(InvariantUtil.isTemplateExpr(r1)) {
            PushTimes(r1, r2)
          } else if(InvariantUtil.isTemplateExpr(r2)){
            PushTimes(r2, r1)
          } else 
            throw IllegalStateException("Expression not linear: " + Times(r1, r2))                     
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal => t
        case fi: FunctionInvocation => fi
        /*case UnaryOperator(e,op) => op(mkLinearRecur(e))
        case BinaryOperator(e1,e2,op) => op(mkLinearRecur(e1),mkLinearRecur(e2))
        case NAryOperator(args,op) => op(args.map(mkLinearRecur(_)))*/
        case _ => throw IllegalStateException("Expression not linear: " + inExpr)
      }
    }
    val rese = mkLinearRecur(atom)
    //println("Unnormalized Linearized expression: "+unnormLinear)
    rese
  }
  
  /**
   * Replaces an expression by another expression in the terms of the given linear constraint.
   */
  def replaceInCtr(replaceMap : Map[Expr,Expr], lc : LinearConstraint) : Option[LinearConstraint] = {
    
    //println("Replacing in "+lc)    
    val newexpr = ExpressionTransformer.simplify(simplifyArithmetic(replace(replaceMap, lc.expr)))
    //println("new expression: "+newexpr)
    
    if(newexpr == tru) None
    else {
      val res = tryExprToTemplate(newexpr)      
      if(res.isEmpty) None
      else {
        val resctr = res.get.asInstanceOf[LinearConstraint]
        //println("resulting constraint: " + resctr)
        Some(resctr)
      }      
    }
  }
  
    /**
   * Eliminates the specified variables from a conjunction of linear constraints (a disjunct) (that is satisfiable)
   * We assume that the disjunct is in nnf form
   */
  def apply1PRuleOnDisjunct(linearCtrs: Seq[LinearConstraint], elimVars: Set[Identifier]): Seq[LinearConstraint] = {    
    //eliminate one variable at a time
    //each iteration produces a new set of linear constraints
    elimVars.foldLeft(linearCtrs)((acc, elimVar) => {
      apply1PRuleOnDisjunct(acc, elimVar)
    })
  }
    
  def apply1PRuleOnDisjunct(linearCtrs: Seq[LinearConstraint], elimVar: Identifier): Seq[LinearConstraint] = {
    
    //collect all relevant constraints
    val emptySeq = Seq[LinearConstraint]()
    val (relCtrs, rest) = linearCtrs.foldLeft((emptySeq,emptySeq))((acc,lc) => {
      if(variablesOf(lc.expr).contains(elimVar)) {
        (lc +: acc._1,acc._2)        
      } else {
        (acc._1,lc +: acc._2)
      }        
    })        
    
    //now consider each constraint look for (a) equality involving the elimVar or (b) check if all bounds are lower
    //or (c) if all bounds are upper.    
    var elimExpr : Option[Expr] = None
    var elimCtr : Option[LinearConstraint] = None
    var allUpperBounds : Boolean = true
    var allLowerBounds : Boolean = true

    relCtrs.foreach((lc) => {
      if (!elimExpr.isDefined) {
        //check for an equality
        if (lc.expr.isInstanceOf[Equals] && lc.coeffMap.contains(elimVar.toVariable)) {

          //println("Found equality for "+elimVar+" : "+lc)
          //if the coeffcient of elimVar is +ve the the sign of the coeff of every other term should be changed
          val IntLiteral(elimCoeff) = lc.coeffMap(elimVar.toVariable)
          val changeSign = if (elimCoeff > 0) true else false

          val startval = if (lc.const.isDefined) {
            val IntLiteral(cval) = lc.const.get
            val newconst = if (changeSign) -cval else cval
            IntLiteral(newconst)

          } else zero

          val substExpr = lc.coeffMap.foldLeft(startval: Expr)((acc, summand) => {
            val (term, IntLiteral(coeff)) = summand
            if (term != elimVar.toVariable) {

              val newcoeff = if (changeSign) -coeff else coeff
              val newsummand = Times(term, IntLiteral(newcoeff))
              if (acc == zero) newsummand
              else Plus(acc, newsummand)

            } else acc
          })

          elimExpr = Some(substExpr)
          elimCtr = Some(lc)
          
        } else if ((lc.expr.isInstanceOf[LessEquals] || lc.expr.isInstanceOf[LessThan]) 
            && lc.coeffMap.contains(elimVar.toVariable)) {

          val IntLiteral(elimCoeff) = lc.coeffMap(elimVar.toVariable)
          if (elimCoeff > 0) {
            //here, we have found an upper bound
            allLowerBounds = false
          } else {
            //here, we have found a lower bound
            allUpperBounds = false
          }
        } else {
          //here, we assume that the operators are normalized to Equals, LessThan and LessEquals
          throw new IllegalStateException("LinearConstraint not in expeceted form : " + lc.expr)
        }
      }
    })

    val newctrs = if (elimExpr.isDefined) {

      //println("Eliminating "+elimVar+" using "+elimExpr.get)
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

    } else if (allLowerBounds || allUpperBounds) {
      //here, drop all relCtrs. None of them are important
      Seq()
    } else {
      //cannot eliminate the variable
      relCtrs
    }
    val resctrs = (newctrs ++ rest)
    //println("After eliminating: "+elimVar+" : "+resctrs)
    resctrs
  }  
}