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

//a collections of utility methods that manipulate the templates
object LinearConstraintUtil {
  val zero = IntLiteral(0)
  val one = IntLiteral(1)
  val mone = IntLiteral(-1)
  val tru = BooleanLiteral(true)
  
  //some utility methods
  def getFIs(ctr: LinearConstraint): Set[FunctionInvocation] = {
    val fis = ctr.coeffMap.keys.collect((e) => e match {
      case fi: FunctionInvocation => fi
    })
    fis.toSet
  }
  
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
    val BinaryOperator(lhs, IntLiteral(0), op) = linearExpr
    if (lhs.isInstanceOf[IntLiteral])
      throw IllegalStateException("relation on two integers, not in canonical form: " + linearExpr)

    val minterms =  getMinTerms(lhs)

    //handle each minterm
    minterms.foreach((minterm: Expr) => minterm match {
      case _ if (Util.isTemplateExpr(minterm)) => {
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
          case _ if (Util.isTemplateExpr(e1)) => {
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
          val isReal = Util.hasReals(e1) || Util.hasReals(e2) 
          //doing something else ... ?
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
          val (r2, const) = simplifyConsts(r)
          val finale = if (r2.isDefined) {
            if (const != 0) Plus(r2.get, IntLiteral(const))
            else r2.get
          } else IntLiteral(const)
          //println(r + " simplifies to "+finale)
          newop(finale, zero)
        }
        case Minus(e1, e2) => Plus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(e1, e2) => {
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          
          if(Util.isTemplateExpr(r1)) {
            PushTimes(r1, r2)
          } else if(Util.isTemplateExpr(r2)){
            PushTimes(r2, r1)
          } else 
            throw IllegalStateException("Expression not linear: " + Times(r1, r2))                     
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal => t
        case fi: FunctionInvocation => fi
        case _ => throw IllegalStateException("Expression not linear: " + inExpr)
      }
    }    
    val rese = mkLinearRecur(atom)   
    rese
  }
  
  /**
   * Replaces an expression by another expression in the terms of the given linear constraint.
   */
  def replaceInCtr(replaceMap : Map[Expr,Expr], lc : LinearConstraint) : Option[LinearConstraint] = {
    
    //println("Replacing in "+lc+" repMap: "+replaceMap)    
    val newexpr = ExpressionTransformer.simplify(simplifyArithmetic(replace(replaceMap, lc.toExpr)))
    //println("new expression: "+newexpr)
    
    if(newexpr == tru) None
    else {
      val res = tryExprToTemplate(newexpr)      
      if(res.isEmpty) None
      else {
        val resctr = res.get.asInstanceOf[LinearConstraint]        
        if(ExpressionTransformer.simplify(resctr.toExpr) == tru) None
        else Some(resctr)
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
          val IntLiteral(elimCoeff) = lc.coeffMap(elimVar.toVariable)
          //make sure the value of the coefficient is 1 or  -1
          //TODO: handle cases wherein the coefficient is not 1 or -1
          if (elimCoeff == 1 || elimCoeff == -1) {
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
                val newsummand = if (newcoeff == 1) term else Times(term, IntLiteral(newcoeff))
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
    if(!currExpr.isInstanceOf[IntLiteral]) {
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
  
}
  
  