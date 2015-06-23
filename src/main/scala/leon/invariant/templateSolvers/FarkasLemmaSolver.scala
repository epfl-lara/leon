package leon
package invariant.templateSolvers

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import solvers.SimpleSolverAPI

import invariant.engine._
import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure._

class FarkasLemmaSolver {
  private val zero = InfiniteIntegerLiteral(0)
  private val one = InfiniteIntegerLiteral(1)
  //for debugging
  private var cvarsSet = Set[Expr]()

  /**
   * This procedure produces a set of constraints that need to be satisfiable for the
   * conjunction ants and conseqs to be false
   * antsSimple - antecedents without template variables
   * antsTemp - antecedents with template variables
   * Similarly for conseqsSimple and conseqsTemp
   *
   * Let A,A' and C,C' denote the simple and templated portions of the antecedent and the consequent respectively.
   * We need to check \exists a, \forall x, A[x] ^ A'[x,a] ^ C[x] ^ C'[x,a] = false
   *
   */
  def constraintsForUnsat(linearCtrs: Seq[LinearConstraint], temps: Seq[LinearTemplate]): Expr = {

    //for debugging
    /*println("#" * 20)
    println(allAnts + " ^ " + allConseqs)
    println("#" * 20)*/
    this.applyFarkasLemma(linearCtrs ++ temps, Seq(), true)
  }

  /**
   * This procedure produces a set of constraints that need to be satisfiable for the implication to hold
   * antsSimple - antecedents without template variables
   * antsTemp - antecedents with template variables
   * Similarly for conseqsSimple and conseqsTemp
   *
   * Let A,A' and C,C' denote the simple and templated portions of the antecedent and the consequent respectively.
   * We need to check \exists a, \forall x, A[x] ^ A'[x,a] => C[x] ^ C'[x,a]
   *
   */
  def constraintsForImplication(antsSimple: Seq[LinearConstraint], antsTemp: Seq[LinearTemplate],
    conseqsSimple: Seq[LinearConstraint], conseqsTemp: Seq[LinearTemplate],
    uisolver: SimpleSolverAPI): Expr = {

    val allAnts = antsSimple ++ antsTemp
    val allConseqs = conseqsSimple ++ conseqsTemp
    //for debugging
    println("#" * 20)
    println(allAnts + " => " + allConseqs)
    println("#" * 20)


    //Optimization 1: Check if ants are unsat (already handled)
    val pathVC = createAnd(antsSimple.map(_.toExpr).toSeq ++ conseqsSimple.map(_.toExpr).toSeq)
    val notPathVC = And(createAnd(antsSimple.map(_.toExpr).toSeq),Not(createAnd(conseqsSimple.map(_.toExpr).toSeq)))
    val (satVC, _) = uisolver.solveSAT(pathVC)
    val (satNVC,_) = uisolver.solveSAT(notPathVC)

    //Optimization 2: use the unsatisfiability of VC and not VC to simplify the constraint generation
    //(a) if A => C is false and A' is true then the entire formula is unsat
    //(b) if A => C is false and A' is not true then we need to ensure A^A' is unsat (i.e, disable Ant)
    //(c) if A => C is true (i.e, valid) then it suffices to ensure A^A' => C' is valid
    //(d) if A => C is neither true nor false then we cannot do any simplification
    //TODO: Food for thought:
    //(a) can we do any simplification for case (d) with the model
    //(b) could the linearity in the disabled case be exploited
    val (ants, conseqs, disableFlag) = (satVC, satNVC) match {
      case (Some(false), _) if (antsTemp.isEmpty) => (Seq(), Seq(), false)
      case (Some(false), _) => (allAnts, Seq(), true) //here only disable the antecedents
      case (_, Some(false)) => (allAnts, conseqsTemp, false) //here we need to only check the inductiveness of the templates
      case _ => (allAnts, allConseqs, false)
    }
    if (ants.isEmpty) {
      BooleanLiteral(false)
    }
    else{
      this.applyFarkasLemma(ants, conseqs, disableFlag)
    }
  }


  /**
   * This procedure uses Farka's lemma to generate a set of non-linear constraints for the input implication.
   * Note that these non-linear constraints are in real arithmetic.
   * TODO: Correctness issue: need to handle strict inequalities in consequent
   * Do we really need the consequent ??
   */
  def applyFarkasLemma(ants: Seq[LinearTemplate], conseqs: Seq[LinearTemplate], disableAnts: Boolean): Expr = {

    //compute the set of all constraint variables in ants
    val antCVars = ants.foldLeft(Set[Expr]())((acc, ant) => acc ++ ant.coeffTemplate.keySet)

    //the creates constraints for a single consequent
    def createCtrs(conseq: Option[LinearTemplate]): Expr = {
      //create a set of identifiers one for each ants
      val lambdas = ants.map((ant) => (ant -> Variable(FreshIdentifier("l", RationalType, true)))).toMap
      val lambda0 = Variable(FreshIdentifier("l", RationalType, true))

      //add a bunch of constraints on lambdas
      var strictCtrLambdas = Seq[Variable]()
      val lambdaCtrs = (ants.collect((ant) => ant.template match {
        case t: LessEquals => GreaterEquals(lambdas(ant), zero)
        case t: LessThan => {
          val l = lambdas(ant)
          strictCtrLambdas :+= l
          GreaterEquals(l, zero)
        }
      }).toSeq :+ GreaterEquals(lambda0, zero))

      //add the constraints on constant terms
      val sumConst = ants.foldLeft(UMinus(lambda0): Expr)((acc, ant) => ant.constTemplate match {
        case Some(d) => Plus(acc, Times(lambdas(ant), d))
        case None => acc
      })

      val cvars = antCVars ++ (if(conseq.isDefined) conseq.get.coeffTemplate.keys else Seq())
      //for debugging
      cvarsSet ++= cvars
      //println("CVars: "+cvars.size)

      //initialize enabled and disabled parts
      var enabledPart: Expr = if (conseq.isDefined) {
        conseq.get.constTemplate match {
          case Some(d) => Equals(d, sumConst)
          case None => Equals(zero, sumConst)
        }
      } else null
      //the disabled part handles strict inequalities as well using Motzkin's transposition
      var disabledPart: Expr =
        if(strictCtrLambdas.isEmpty) Equals(one, sumConst)
        else Or(Equals(one, sumConst),
          And(Equals(zero, sumConst),createOr(strictCtrLambdas.map(GreaterThan(_,zero)))))

      for (cvar <- cvars) {
        //compute the linear combination of all the coeffs of antCVars
        //println("Processing cvar: "+cvar)
        var sumCoeff: Expr = zero
        for (ant <- ants) {
          //handle coefficients here
          if (ant.coeffTemplate.contains(cvar)) {
            val addend = Times(lambdas(ant), ant.coeffTemplate.get(cvar).get)
            if (sumCoeff == zero)
              sumCoeff = addend
            else
              sumCoeff = Plus(sumCoeff, addend)
          }
        }
        //println("sum coeff: "+sumCoeff)
        //make the sum equal to the coeff. of cvar in conseq
        if (conseq.isDefined) {
          enabledPart = And(enabledPart,
            (if (conseq.get.coeffTemplate.contains(cvar))
              Equals(conseq.get.coeffTemplate.get(cvar).get, sumCoeff)
            else Equals(zero, sumCoeff)))
        }

        disabledPart = And(disabledPart, Equals(zero, sumCoeff))
      } //end of cvars loop

      //the final constraint is a conjunction of lambda constraints and disjunction of enabled and disabled parts
      if (disableAnts) And(createAnd(lambdaCtrs), disabledPart)
      else {
        //And(And(lambdaCtrs), enabledPart)
        And(createAnd(lambdaCtrs), Or(enabledPart, disabledPart))
       }
    }

    val ctrs = if (disableAnts) {
      //here conseqs are empty
      createCtrs(None)
    } else {
      val Seq(head, tail @ _*) = conseqs
      val nonLinearCtrs = tail.foldLeft(createCtrs(Some(head)))((acc, conseq) => And(acc, createCtrs(Some(conseq))))
      nonLinearCtrs
    }
    ExpressionTransformer.IntLiteralToReal(ctrs)
  }
}