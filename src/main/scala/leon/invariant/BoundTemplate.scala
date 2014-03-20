package leon
package invariant

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
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
import leon.verification.Tactic
import leon.verification.VerificationReport
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }

/**
 * This template generator creates a bound template for the result of a function if it returns an integer value
 */
/*class BoundTemplate(prog: Program, reporter: Reporter) extends TemplateGenerator {

  private val zero = IntLiteral(0)
  var attempt = 0

  def getNextTemplate(fd: FunDef): Expr = {     
    //first time ?
    if(attempt <= 0){
      attempt += 1
      //checks if there exists an upper or lower bound
      val boundTemp = if (fd.returnType == Int32Type) {
        val retTerm = InvariantUtil.getFunctionReturnVariable(fd)
        val argTerms = fd.args.filter((vardecl) => vardecl.tpe == Int32Type).map(_.toVariable)
        val rhs = argTerms.foldLeft(TemplateIdFactory.freshTemplateVar(): Expr)((acc, t) => {
          Plus(Times(TemplateIdFactory.freshTemplateVar(), t), acc)
        })
        val retCoeff = TemplateIdFactory.freshTemplateVar()        
         
        And(LessEquals(Times(retCoeff,retTerm), rhs),Not(Equals(retCoeff,zero)))
      } else {
        LessEquals(TemplateIdFactory.freshTemplateVar(), IntLiteral(0))
      }      
      boundTemp      
    } else {
      //this should have a solution
      LessEquals(TemplateIdFactory.freshTemplateVar(), IntLiteral(0))
    }        
  }
}*/