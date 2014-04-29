package leon
package invariant.util
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import java.io._
import solvers._
import solvers.z3._
import leon.invariant._
import scala.util.control.Breaks._
import RealValuedExprInterpreter.evaluate
import RealValuedExprInterpreter.evaluateRealPredicate
import RealValuedExprInterpreter.floor
import RealValuedExprInterpreter.isGEZ
import scala.reflect.runtime.universe

import invariant.engine.InferenceContext
import invariant.factories._

class Minimizer(ctx: InferenceContext) {
  
  private val debugMinimization = true
  /**
   * Here we are assuming that that initModel is a model for ctrs
   * TODO: make sure that the template for rootFun is the time template      
   */
  val MaxIter = 16 //note we may not be able to represent anything beyond 2^16
  val MaxInt = Int.MaxValue
  val sqrtMaxInt = 45000 //this is a number that is close a sqrt of 2^31 
 val half = RealLiteral(1, 2)
  val two = RealLiteral(2, 1)
  val rzero = RealLiteral(0, 1)
  val mone = RealLiteral(-1, 1)
  
  private val program = ctx.program
  private val leonctx = ctx.leonContext 

  //for statistics and output
  //store the lowerbounds for each template variables in the template of the rootFun provided it is a time template
  var lowerBoundMap = Map[Variable, RealLiteral]()
  def updateLowerBound(tvar: Variable, rval: RealLiteral) = {
    //record the lower bound if it exist
    if (lowerBoundMap.contains(tvar)) {
      lowerBoundMap -= tvar
    }
    lowerBoundMap += (tvar -> rval)
  }

  import RealValuedExprInterpreter._
  def tightenTimeBounds(timeTemplate: Expr, inputCtr: Expr, initModel: Map[Identifier, Expr]): Map[Identifier, Expr] = {
    //the order in which the template variables are minimized is based on the level of nesting of the  terms
    val tempvarNestMap: Map[Variable, Int] = computeCompositionLevel(timeTemplate)
    val orderedTempVars = tempvarNestMap.toSeq.sortWith((a, b) => a._2 >= b._2).map(_._1)    

    //do a binary search on sequentially on each of these tempvars      
    val solver = SimpleSolverAPI(
      new TimeoutSolverFactory(SolverFactory(() => new UIFZ3Solver(leonctx, program) with TimeoutSolver),ctx.timeout * 1000))       

    println("minimizing...")
    var currentModel = initModel    
    orderedTempVars.foldLeft(inputCtr: Expr)((acc, tvar) => {
     
      var upperBound = if (currentModel.contains(tvar.id)) {
        currentModel(tvar.id).asInstanceOf[RealLiteral]
      } else {
        initModel(tvar.id).asInstanceOf[RealLiteral]
      }
      //note: the lower bound is an integer by construction
      var lowerBound: Option[RealLiteral] = if (tvar == orderedTempVars(0) && lowerBoundMap.contains(tvar)) 
    	  										Some(lowerBoundMap(tvar)) 
    	  										else None

      //a helper method
      def updateState(nmodel: Map[Identifier, Expr]) = {
        upperBound = nmodel(tvar.id).asInstanceOf[RealLiteral]
        //complete the new model if necessary
        currentModel = nmodel
        if (this.debugMinimization)
          println("Found new upper bound: " + upperBound)
      }
      
      if (this.debugMinimization) {
        println("Minimizing variable: " + tvar + " Initial Bounds: [" + upperBound +","+
            (if(lowerBound.isDefined) lowerBound.get else "_")+"]")
      }

      //TODO: use incremental solving of z3 here (however make sure there is no bug)
      var continue = true
      var iter = 0
      do {
        iter += 1
        //here we perform some sanity checks to prevent overflow
        if (!boundSanityChecks(upperBound, lowerBound)) {
          //println("Escaping as bound sanity checks do not hold: "+lowerBound.get)
          //here again check if we can continue with the floor                 
          val (res, newModel) = solver.solveSAT(And(acc, Equals(tvar, floor(upperBound))))
          if (res == Some(true))
            updateState(newModel)
          else {
            println("Bound sanity checks failed")
            continue = false
          }
        }
        if (continue) {
          //we make sure that curr val is an integer
          val currval = if (lowerBound.isDefined) {
            val midval = evaluate(Times(half, Plus(upperBound, lowerBound.get)))
            floor(midval)

          } else {
            val rlit @ RealLiteral(n, d) = upperBound
            if (isGEZ(rlit)) {
              if (n == 0) {
                //make the upper bound negative 
                mone
              } else {
                floor(evaluate(Times(half, upperBound)))
              }
            } else floor(evaluate(Times(two, upperBound)))
          }

          //check if the lowerbound, if it exists, is < currval
          if (lowerBound.isDefined && evaluateRealPredicate(GreaterEquals(lowerBound.get, currval))) {
            continue = false
          } else {
            val boundCtr = if (lowerBound.isDefined) {
              And(LessEquals(tvar, currval), GreaterEquals(tvar, lowerBound.get))
            } else LessEquals(tvar, currval)

            //val t1 = System.currentTimeMillis()            
            val (res, newModel) = solver.solveSAT(And(acc, boundCtr))
            //val t2 = System.currentTimeMillis()
            //println((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
            res match {
              case Some(true) => {
                //here we have a new upper bound and also a newmodel
                val newval = newModel(tvar.id).asInstanceOf[RealLiteral]
                if (newval.hasOverflow) {
                  //try to see if the floor (using integer division instead) of the overflowed value is a model
                  val (n, d) = newval.getBigRealValue.get
                  val flval = RealLiteral((n / d).intValue, 1)
                  val (res, secondModel) = solver.solveSAT(And(acc, Equals(tvar, flval)))
                  res match {
                    case Some(true) => {
                      println("handled overflow successfully...")
                      updateState(secondModel)
                    }
                    case _ => {
                      if (this.debugMinimization)
                        println("Aborting due to overflow.")
                      continue = false
                    }
                  }
                } else updateState(newModel)
              }
              case _ => {
                //here we have a new lower bound: currval
                lowerBound = Some(currval)
                if (this.debugMinimization)
                  println("Found new lower bound: " + currval)
              }
            }
          }
        }
      } while (continue && iter < MaxIter)
      
      //this is the last ditch effort to make the upper bound constant smaller.
      //check if the floor of the upper-bound is a solution
      val currval@RealLiteral(n,d) = currentModel(tvar.id)
      if (d != 1) {        
        val (res, newModel) = solver.solveSAT(And(acc, Equals(tvar, floor(currval))))        
        if(res == Some(true)) 
          updateState(newModel)          
      }
        
      //here, we found a best-effort minimum
      if (lowerBound.isDefined) {
        updateLowerBound(tvar, lowerBound.get)
      }
      And(acc, Equals(tvar, currentModel(tvar.id)))
    })        
    
    println("Minimization complete...")
    initModel.keys.map((id) => {
      if (currentModel.contains(id))
        (id -> currentModel(id))
      else
        (id -> initModel(id))
    }).toMap
  }

  def checkBoundingInteger(tvar: Variable, rl: RealLiteral, nlctr: Expr, solver: SimpleSolverAPI): Option[Map[Identifier, Expr]] = {
    val nl@RealLiteral(n, d) = normalize(rl)
    if (d != 1) {      
      val flval = floor(nl)
      val (res, newModel) = solver.solveSAT(And(nlctr, Equals(tvar, flval)))
      res match {
        case Some(true) => Some(newModel)
        case _ => None
      }
    } else None
  } 

  /**
   * These checks are performed to avoid an overflow during the computation of currval
   */
  def boundSanityChecks(ub: RealLiteral, lb: Option[RealLiteral]): Boolean = {
    val RealLiteral(n, d) = ub
    if (n <= (MaxInt / 2)) {
      if (lb.isDefined) {
        val RealLiteral(n2, _) = lb.get
        (n2 <= sqrtMaxInt && d <= sqrtMaxInt)
      } else {
        (d <= (MaxInt / 2))
      }
    } else false
  }

  /**
   * The following code is little tricky
   */
  def computeCompositionLevel(template: Expr): Map[Variable, Int] = {
    var nestMap = Map[Variable, Int]()

    def updateMax(v: Variable, level: Int) = {
      println("Nesting level: " + v + "-->" + level)
      if (nestMap.contains(v)) {
        if (nestMap(v) < level) {
          nestMap -= v
          nestMap += (v -> level)
        }
      } else
        nestMap += (v -> level)
    }

    def functionNesting(e: Expr): Int = {
      //println("NestExpr: " + e)
      e match {

        case Times(e1, v @ Variable(id)) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e1)
          updateMax(v, nestLevel)
          nestLevel
        }
        case Times(v @ Variable(id), e2) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          val nestLevel = functionNesting(e2)
          updateMax(v, nestLevel)
          nestLevel
        }
        case v @ Variable(id) if (TemplateIdFactory.IsTemplateIdentifier(id)) => {
          updateMax(v, 0)
          0
        }
        case FunctionInvocation(_, args) => 1 + args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
        case t: Terminal => 0
        case UnaryOperator(arg, _) => functionNesting(arg)
        case BinaryOperator(a1, a2, _) => functionNesting(a1) + functionNesting(a2)
        case NAryOperator(args, _) => args.foldLeft(0)((acc, arg) => acc + functionNesting(arg))
      }
    }
    functionNesting(template)
    nestMap
  }

}