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
import scala.collection.mutable.{ Set => MutableSet }

class TemplateFactory {

  //a mapping from function definition to the variables in its templates
  private var paramCoeff = Map[FunDef, List[Variable]]()

  /**
   * The ordering of the expessions in the List[Expr] is very important.
   * TODO: correctness issue: flatten the functions in the template
   * TODO: Feature: 
   * (a) allow template functions and functions with template variables
   * (b) allow template ADTs
   * (c) do we need to consider sophisticated ways of constructing terms ?  
   */
  def getTypedCompositeTerms(baseTerms: Seq[Expr]): List[Expr] = {

    //just consider all the baseTerms that are integers    
    val terms = baseTerms.collect((e: Expr) => e match { case _ if (e.getType == Int32Type) => e })
    terms.toList
  }

  def constructTemplate(baseTerms: Seq[Expr], fd: FunDef): Set[LinearTemplate] = {
    //check if a template has been instantiated for the function
    if (!paramCoeff.contains(fd)) {
      //bind function to (unknown) coefficients
      val params = fd.args.map(_.toVariable)
      val dummycall = FunctionInvocation(fd, params)
      val paramTerms = getTypedCompositeTerms(params :+ dummycall)
      //note that the template variables may have real types
      val newCoeffs = List.range(0, paramTerms.size + 1).map((i) => Variable(FreshIdentifier("a" + i + "a", true).setType(RealType)))
      paramCoeff += (fd -> newCoeffs)
    }

    //get all the composite terms constructible using the base terms
    val allTerms = getTypedCompositeTerms(baseTerms)

    //parse the existing coefficient map
    val (constPart :: coeffsPart) = paramCoeff(fd)
    val coeffmap = allTerms.zip(coeffsPart)

    //create a linear expression
    val linearExpr = LessEquals(coeffmap.foldLeft(constPart: Expr)((acc, param) => {
      val (term, coeff) = param
      Plus(acc, Times(coeff, term))
    }), IntLiteral(0))

    Set(LinearTemplate(linearExpr, coeffmap.toMap, Some(constPart)))
  }
  
  def getTemplateSynthesizer(): ((Seq[Expr],FunDef) => Set[LinearTemplate]) =  constructTemplate  

/*  def getTemplateSynthesizer(): (FunctionInvocation => Set[LinearTemplate]) = {

    (fi: FunctionInvocation) =>
      {               
        //get the arguments of the function invocation
        val args = fi.args
        //here check if the args are all Terminals
        args.foreach((arg) => if (!arg.isInstanceOf[Terminal]) throw IllegalStateException("Argument is not a variable"))
        constructTemplate(args :+ fi, fi.funDef)
      }
  }*/
}