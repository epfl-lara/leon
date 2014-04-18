package leon
package invariant.factories

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import java.io._
import leon.invariant._
import scala.util.control.Breaks._
import scala.concurrent._
import scala.concurrent.duration._

import invariant.engine._
import invariant.util._
import invariant.structure._

class AxiomFactory(ctx : InferenceContext) {                       
  
  val tru = BooleanLiteral(true)  
  //Add more axioms here, if necessary  
  def hasUnaryAxiom(call: Call) : Boolean = {
    //important: here we need to avoid applying commutativity on the calls produced by axioms instantiation
    val funinfo = FunctionInfoFactory.getFunctionInfo(call.fi.tfd.fd)
    (funinfo.isDefined && funinfo.get.doesCommute) 
  }
    
  def hasBinaryAxiom(call: Call) : Boolean = {
    val funinfo = FunctionInfoFactory.getFunctionInfo(call.fi.tfd.fd)
    (funinfo.isDefined && 
        (funinfo.get.hasMonotonicity || funinfo.get.hasDistributivity))
  }
  
  def unaryAxiom(call: Call) : (Expr,Expr) = {
    val callee = call.fi.tfd.fd
    val tfd = call.fi.tfd    
    
    val funinfo = FunctionInfoFactory.getFunctionInfo(callee)
    if(funinfo.isDefined && funinfo.get.doesCommute) {
      //note: commutativity is defined only for binary operations
      val Seq(a1, a2) = call.fi.args
      val newret = TVarFactory.createTemp("cm").toVariable
      val newfi = FunctionInvocation(tfd,Seq(a2,a1))
      val newcall = Call(newret,newfi)      
      (tru, And(newcall.toExpr, Equals(newret, call.retexpr)))
    } else 
      throw IllegalStateException("Call does not have unary axiom: "+call)
  }

  def binaryAxiom(call1: Call, call2: Call): Seq[(Expr,Expr)] = {

    if (call1.fi.tfd.id != call2.fi.tfd.id)
      throw IllegalStateException("Instantiating binary axiom on calls to different functions: " + call1 + "," + call2)

    if (!hasBinaryAxiom(call1))
      throw IllegalStateException("Call does not have binary axiom: " + call1)

    val callee = call1.fi.tfd.fd    
    val funinfo = FunctionInfoFactory.getFunctionInfo(callee)
    //monotonicity
    var axioms = if (funinfo.get.hasMonotonicity) {
      Seq(monotonizeCalls(call1, call2))
    } else Seq()
    
    //distributivity
    axioms ++= (if (funinfo.get.hasDistributivity) {
      //println("Applying distributivity on: "+(call1,call2))
      Seq(undistributeCalls(call1, call2))
    } else Seq())
    
    axioms
  }
  
  def monotonizeCalls(call1: Call, call2: Call): (Expr,Expr) = {    
    val ants = (call1.fi.args zip call2.fi.args).foldLeft(Seq[Expr]())((acc, pair) => {
      val lesse = LessEquals(pair._1, pair._2)
      lesse +: acc
    })
    val conseq = LessEquals(call1.retexpr, call2.retexpr)
    (And(ants), conseq)    
  }
   
  //this is applicable only to binary operations
  def undistributeCalls(call1: Call, call2: Call): (Expr,Expr) = {    
    val fd = call1.fi.tfd.fd
    val tfd = call1.fi.tfd    
    
    val Seq(a1,b1) = call1.fi.args
    val Seq(a2,b2) = call2.fi.args
    val r1 = call1.retexpr
    val r2 = call2.retexpr
    
    val dret1 = TVarFactory.createTemp("dt").setType(Int32Type).toVariable
    val dret2 = TVarFactory.createTemp("dt").setType(Int32Type).toVariable
    val dcall1 = Call(dret1, FunctionInvocation(tfd,Seq(a2,Plus(b1,b2))))
    val dcall2 = Call(dret2, FunctionInvocation(tfd,Seq(Plus(a1,a2),b2)))    
    //val axiom1 = Implies(LessEquals(a1,a2), And(LessEquals(Plus(r1,r2),dret1), dcall1.toExpr)) 
    //val axiom2 = Implies(LessEquals(b1,b2), And(LessEquals(Plus(r1,r2),dret2), dcall2.toExpr))
//    And(axiom1,axiom2)
    (LessEquals(b1,b2), And(LessEquals(Plus(r1,r2),dret2), dcall2.toExpr))
  }
}
