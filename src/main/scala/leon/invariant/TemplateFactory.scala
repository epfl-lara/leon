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

class TemplateIdentifier(override val id: Identifier) extends Variable(id)

/**
 * Templates are expressions with template variables.
 * The program variables that can be free in the templates are only the arguments and
 * the result variable
 */
object TemplateFactory {

  //a mapping from function definition to the template
  private var templateMap = Map[FunDef, Expr]()
  
  //a set of template ids
  private var ids = Set[Identifier]()
  
  def freshIdentifier(name : String = "") : Identifier = {
    val idname = if(name.isEmpty()) "a?"
    			 else name + "?"
    val freshid = FreshIdentifier(idname, true).setType(RealType)
    ids += freshid
    freshid
  }
  
   /**
   * Template variables have real type
   */
  def IsTemplateIdentifier(id : Identifier) : Boolean = {
    ids.contains(id)
  }
  
  def IsTemplateVar(v : Variable) : Boolean = {
    IsTemplateIdentifier(v.id)
  }
   
  def freshTemplateVar(name : String= "") : Variable = {
    Variable(freshIdentifier(name))
  }
  
  def setTemplate(fd:FunDef, tempExpr :Expr) = {
    templateMap += (fd -> tempExpr) 
  }

  /**    
   * This is the default template generator 
   * TODO: Feature: 
   * (a) allow template functions and functions with template variables
   * (b) allow template ADTs
   * (c) do we need to consider sophisticated ways of constructing terms ?  
   */
  def getDefaultTemplate(fd : FunDef): Expr = {

    //just consider all the arguments, return values that are integers
    val baseTerms = fd.args.filter((vardecl) => vardecl.tpe == Int32Type).map(_.toVariable) ++ 
    					(if(fd.returnType == Int32Type) Seq(ResultVariable()) else Seq())        
    					
    val lhs = baseTerms.foldLeft(freshTemplateVar() : Expr)((acc, t)=> {       
       Plus(Times(freshTemplateVar(),t),acc)
    })
    val tempExpr = LessEquals(lhs,IntLiteral(0))
    tempExpr
  }

  /**
   * Constructs a template using a mapping from the formals to actuals
   */
  def constructTemplate(argmap: Map[Expr,Expr], fd: FunDef): Expr = {
    
    //initialize the template for the function
    if (!templateMap.contains(fd)) {      
      templateMap += (fd -> getDefaultTemplate(fd))
    }        
    replace(argmap,templateMap(fd))
  }
  
  def getTemplate(fd : FunDef) : Option[Expr] = {
    templateMap.get(fd)
  }   

  def getFunctionsWithTemplate : Seq[FunDef] = templateMap.keys.toSeq

}