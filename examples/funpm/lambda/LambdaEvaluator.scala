/** ================================================= 
 *  Evaluator for the untyped lambda calculus using
 *  The de Bruijn notation for lambda-terms
 * =================================================
 */ 

package funpm.lambda

/** =================================================
 *      Lambda Terms for Untyped Lambda Calculus
 *  =================================================
 */

sealed abstract case class Term() {
  def isSame(t: Term): Boolean = this match {
    case Const => true
    
    case Var(x) => t match {
      case Var(y) => x == y
      case _ if !t.isInstanceOf[Var] => false
    }
    
    case Abstr(t1) => t match {
      case Abstr(t2) => t1.isSame(t2)
      case _ if !t.isInstanceOf[Abstr] => false
    }
      
    case App(t1,t2) => t match {
      case App(t21,t22) => t1.isSame(t21) && t2.isSame(t22)
      case _ if !t.isInstanceOf[App] => false
    }
  }
}

case object Const extends Term
case class Var(val index: Int) extends Term
case class Abstr(val t: Term) extends Term
case class App(val t1: Term, val t2: Term) extends Term

/** =================================================
 *                 Lambda Terms Evaluator
 *                       CallByValue
 *  =================================================
 */


class Eval {
  
  def reduce(t: Term): Term =
    if(this.reduceCallByValue(t).isSame(t)) { t }
    else { this.reduce(this.reduceCallByValue(t)) }
  
  def isValue(t: Term): Boolean =
    /* postcondition   t \in Abstr <--> res == true
    */
    t.isInstanceOf[Abstr]
  
  def reduceCallByValue(t: Term): Term = (t : Term) match {
      
    case App(Abstr(t1:Term),v2:Term) if this.isValue(v2) =>
      this.subst(t1,1,v2)
  
    case App(v1: Abstr, t2: Term) if !this.isValue(t2) =>
      App(v1, this.reduceCallByValue(t2))

    case App(t1: Term, t2: Term) if !this.isValue(t1) =>
      App(this.reduceCallByValue(t1), t2)
        
    case Abstr(t1: Term) => Abstr(this.reduceCallByValue(t1))
    case Var(_) => t
    case Const => t
  }
  
  def subst(t: Term, index: Int, s: Term): Term = t match {
    case Const => t
    
    case Var(y) =>
      if (y == index) { s } else { t }
    
    case Abstr(t1: Term) => Abstr(this.subst(t1,index+1,s))
      
    case App(t1: Term, t2: Term) =>
      App(this.subst(t1,index,s), this.subst(t2,index,s))
  }
  
}

/** =================================================
 *             Printer for Lambda Terms
 *  =================================================
 */

class Printer {
  def prompt(t: Term): Unit = {
    printer(t)
    println
  }
  def printer(t: Term): Unit = t match {
    case Var(x) => print(x)
    case Abstr(t) => print("\\. ("); printer(t); print(")")
    case App(t1,t2) => print("("); printer(t1); print(") ");
                       print("("); printer(t2); print(") ");
  }
}


/** =================================================
 *   \\z. (\\y. y (\\x. x)) (\\x. z x) 
 *   is in de Bruijn notation
 *   \\ (\\ 1 (\\ 1)) (\\ 2 1)
 *   and it evaluates to:
 *   \\ 2 (\\ 1) that is \\z. z (\\x. x)
 *  =================================================
 */ 
object LambdaEvaluator extends Application {

   assert(
     new Eval().reduce(
       Abstr(
         App(
           Abstr(App(Var(1), Abstr(Var(1)))),
           Abstr(App(Var(2),Var(1)))
         )
       )
     )
     ==
     Abstr(App(Var(2), Abstr(Var(1))))
   )
}
