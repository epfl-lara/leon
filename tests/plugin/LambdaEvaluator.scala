package plugin

/** ================================================= 
 *  Evaluator for the untyped lambda calculus using
 *  The de Bruijn notation for lambda-terms
 * =================================================
 */ 

import funcheck.lib.Specs._

object LambdaEvaluator {
  /** =================================================
   *      Lambda Terms for Untyped Lambda Calculus
   *  =================================================
   */
  @generator
  sealed abstract class Term
  case class App(val t1: Term, val t2: Term) extends Term
  case class Abstr(val t: Term) extends Term
  case class Var(val index: Int) extends Term
  case class Const() extends Term
  
  def reduce(that: Term): Term = {
    if(reduceCallByValue(that) == that) 
      that
    else  
      reduce(reduceCallByValue(that))
  }
  
  def isValue(that: Term): Boolean = that.isInstanceOf[Abstr]
  
  def reduceCallByValue(that: Term): Term = that match {
    
    case App(Abstr(t1), v2) if isValue(v2) =>
      subst(t1,1,v2)
  
    case App(v1: Abstr, t2) if !isValue(t2) =>
      App(v1, reduceCallByValue(t2))

    case App(t1, t2) if !isValue(t1) =>
      App(reduceCallByValue(t1), t2)
        
    case Abstr(t1) => Abstr(reduceCallByValue(t1))
    case Var(_) => that
    case Const() => that
  }
  
  def subst(t: Term, index: Int, s: Term): Term = t match {
    case Const() => t
    
    case Var(y) =>
      if (y == index) { s } else { t }
    
    case Abstr(t1: Term) => Abstr(subst(t1,index+1,s))
      
    case App(t1, t2) =>
      App(subst(t1,index,s), subst(t2,index,s))
  }
  
  //forAll[(Term,Int,Term)]{p => p._1 == subst(subst(p._1,p._2,p._3),p._2,p._1)}
  // this (correctly) fails 
  // counter-example: p._1=Var(13) , p._2 = 13 , p._3 = Const()
  
  
  
  def main(args: Array[String]) = {
    /** =================================================
     *   \\z. (\\y. y (\\x. x)) (\\x. z x) 
     *   is in de Bruijn notation
     *   \\ (\\ 1 (\\ 1)) (\\ 2 1)
     *   and it evaluates to:
     *   \\ 2 (\\ 1) that is \\z. z (\\x. x)
     *  =================================================
     */ 
//    assert(
//      reduce(
//        Abstr(
//          App(
//            Abstr(App(Var(1), Abstr(Var(1)))),
//            Abstr(App(Var(2),Var(1)))
//          )
//        )
//      )
//      ==
//      Abstr(App(Var(2), Abstr(Var(1))))
//    )
  }
  
  
}
  


