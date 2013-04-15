package leon
package invariant

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
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
import leon.verification.Tactic
import leon.verification.VerificationReport

class LinearImplicationSolver {
  private val zero = IntLiteral(0)
  private val one = IntLiteral(1)
  //for debugging 
  private var cvarsSet = Set[Expr]()

  /**
   * This procedure uses Farka's lemma to generate a set of non-linear constraints for the input implication.
   * Note that these are non-linear constraints in real arithmetic.
   */    
  def applyFarkasLemma(ants: Seq[LinearTemplate], conseqs: Seq[LinearTemplate], disableAnts: Boolean): Expr = {

    //compute the set of all constraint variables in ants
    val antCVars = ants.foldLeft(Set[Expr]())((acc, ant) => acc ++ ant.coeffTemplate.keySet)

    //the creates constraints for a single consequent
    def createCtrs(conseq: LinearTemplate): Expr = {
      //create a set of identifiers one for each ants            
      val lambdas = ants.map((ant) => (ant -> Variable(FreshIdentifier("l", true).setType(Int32Type)))).toMap
      val lambda0 = Variable(FreshIdentifier("l", true).setType(Int32Type))

      //add a bunch of constraints on lambdas
      val lambdaCtrs = (ants.collect((ant) => ant.template match {
        case t: LessEquals => GreaterEquals(lambdas(ant), zero)
      }).toSeq :+ GreaterEquals(lambda0, zero))

      //add the constraints on constant terms      
      val sumConst = ants.foldLeft(UMinus(lambda0): Expr)((acc, ant) => ant.constTemplate match {
        case Some(d) => Plus(acc, Times(lambdas(ant), d))
        case None => acc
      })

      val cvars = conseq.coeffTemplate.keys ++ antCVars

      //for debugging
      cvarsSet ++= cvars
      //println("CVars: "+cvars.size)

      //initialize enabled and disabled parts
      var enabledPart: Expr = (conseq.constTemplate match {
        case Some(d) => Equals(d, sumConst)
        case None => Equals(zero, sumConst)
      })
      //Fortunately the disbaled case are linear constraints
      var disabledPart: Expr = Equals(one, sumConst)

      //total number of constraint vars
      for (cvar <- cvars) {
        //compute the linear combination of all the coeffs of antCVars
        var sumCoeff: Expr = null
        for (ant <- ants) {
          //handle coefficients here
          if (ant.coeffTemplate.contains(cvar)) {
            val addend = Times(lambdas(ant), ant.coeffTemplate.get(cvar).get)
            if (sumCoeff == null)
              sumCoeff = addend
            else
              sumCoeff = Plus(sumCoeff, addend)
          }
        }
        //make the sum equal to the coeff. of cvar in conseq
        enabledPart = And(enabledPart,
          (if (conseq.coeffTemplate.contains(cvar)) Equals(conseq.coeffTemplate.get(cvar).get, sumCoeff)
          else Equals(zero, sumCoeff)))

        disabledPart = And(disabledPart, Equals(zero, sumCoeff))
      } //end of cvars loop

      //the final constraint is a conjunction of lambda constraints and disjunctioin of enabled and disabled parts
      if (disableAnts) And(And(lambdaCtrs), disabledPart)
      else
        And(And(lambdaCtrs), Or(enabledPart, disabledPart))
    }

    val (head :: tail) = conseqs

    //this is an optimization
    if (disableAnts) {
      //convertIntToReal(createCtrs(head))
      createCtrs(head)
    } else {
      val nonLinearCtrs = tail.foldLeft(createCtrs(head))((acc, conseq) => And(acc, createCtrs(conseq)))
      //convertIntToReal(nonLinearCtrs)
      nonLinearCtrs
    }
  }

  /**
   * converts all integer valued variables and literals to RealType
   */
  def convertIntToReal(inexpr: Expr): Expr = {
    //var intIdToRealId = Map[Identifier, Identifier]()
    val transformer = (e: Expr) => e match {
      case IntLiteral(v) => RealLiteral(v, 1)
      /*case v @ Variable(intId) if (v.getType == Int32Type) => {
        val realId = intIdToRealId.getOrElse(intId, {
          val freshId = FreshIdentifier(intId.name, true).setType(RealType)
          intIdToRealId += (intId -> freshId)
          freshId
        })
        Variable(realId)
      }*/
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }
}