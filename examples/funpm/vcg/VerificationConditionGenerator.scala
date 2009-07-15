/** =================================================
 *          Verification Condition Generator
 * 
 *  Grammar:
 * 
 *  S ::= (v=T)
 *       | assume(F)
 *       | assert(F)
 *       | havoc(v,...,v)
 *       | S ; S
 *       | while  (F) [inv F] { S } 
 *       | if (F) { S } else { S }
 *  T ::= T+T | T-T | K*T | v | K
 *  A ::= T=T | T < T | ITrue | IFalse
 *  F ::= A | (F&F) | (F|F) | ~F | ALL v.F | EX v.F
 *  K ::= 0 | 1 | 2 | ...
 *  v ::= x | y | z | ...
 *  =================================================
 */

package funpm.vcg

/** =================================================
 *           Class hierarchy and Extractors
 *  =================================================
 */

sealed abstract class Tree
abstract class IGuard extends Tree

/** (x = T) */
case class IAssign(val x: String, val t: Term) extends IGuard

/** assume(f) */
case class IAssume(val f: Form) extends IGuard 

/** assert(f) */
case class IAssert(val f: Form) extends IGuard 

/** havoc(v,v,...,v) */
case class IHavoc(val vars: Seq[IVar]) extends IGuard 

/** S ; S */
case class ISequence(val s1: IGuard, val s2: IGuard) extends IGuard 

/** while (cond) { block } */
case class IWhile(val cond: Form, val inv: Form,  val block: IGuard) extends IGuard 

/** if (cond) { then } else { elses }*/
case class IIf(val cond: Form, val then: IGuard, val elses: IGuard) extends IGuard 

abstract class Term extends Tree
/** T + T */
case class IPlus(val t1: Term, val t2: Term) extends Term 

/** T - T */
case class IMinus(val t1: Term, val t2: Term) extends Term 

/** K*T */
case class IProd(val k: IConst, val t: Term) extends Term 

/** v */
case class IVar(val name: String) extends Term 

/** 0 | 1 | 2 | ... */
case class IConst(val number: Int) extends Term 

abstract class Form extends Tree

/** (F & F) */
case class IAnd(val f1: Form, val f2: Form) extends Form 

/** (F | F) */
case class IOr(val f1: Form, val f2: Form) extends Form 

/** ~F */
case class INot(val f: Form) extends Form 

/** EX v.F */
case class IExists(val v: String, val f: Form) extends Form 

/** ALL v.F */
case class IForall(val v: String, val f: Form) extends Form 

abstract class Atom extends Form

/** t1 = t2 */
case class IEqual(val t1: Term, val t2: Term) extends Atom 

/** t1 < t2 */
case class ILess(val t1: Term, val t2: Term) extends Atom 

/** true */
case class ITrue() extends Atom 

/** false */
case class IFalse() extends Atom 

/** =================================================
 *             Substitution
 *  =================================================
 */

object Substitution {
  
  def apply(x: String, s: Term, f: Form): Form = substFormula(x,s,f)
  
  def substFormula(x: String, s: Term, f: Form): Form = f match {
    case IEqual(t1,t2) => IEqual(substTerm(x,s,t1), substTerm(x,s,t2))
    case ILess(t1,t2)  => ILess(substTerm(x,s,t1), substTerm(x,s,t2))
    case IAnd(f1,f2)   => IAnd(substFormula(x,s,f1), substFormula(x,s,f2))
    case IOr(f1,f2)    => IOr(substFormula(x,s,f1), substFormula(x,s,f2))
    case INot(f)       => INot(substFormula(x,s,f))
    
    case IExists(x1,f1) =>
      if(x == x1) { IExists(x1,f1) }
      else {
        if(x != x1 && !FV(x1,s)) { IExists(x1,substFormula(x,s,f1)) }
        else {
          substFormula(x,s,substFormula(x1,IVar(x1+"1"),f))
        }
      }

    case IForall(x1,f1) =>
      if(x==x1) { IForall(x1,f1) } 
      else {
        if(x != x1 && !FV(x1,s)) { IForall(x1,substFormula(x,s,f1)) }
        else {
          substFormula(x,s,IForall(x1+"1",substFormula(x1,IVar(x1+"1"),f1)))
        }
      }

    case ITrue()  => f
    case IFalse() => f
  } 
  
  
  def substTerm(x: String, s: Term, t: Term): Term = t match {
    case IVar(y) if x == y => s /**[x |-> s]x = s*/
    case IVar(y) if x != y => t /**[x |-> s]x = s*/
    case IPlus(t1,t2)      => IPlus(substTerm(x,s,t1),substTerm(x,s,t2))
    case IMinus(t1,t2)     => IMinus(substTerm(x,s,t1),substTerm(x,s,t2))
    case IProd(k,t)        => IProd(k,substTerm(x,s,t))
    case IConst(_)         => t /**[x |-> s] y = y*/
  }
  
  
  def renameFormula(oldx: String, newx: String, f: Form): Form = f match {
    case IExists(x,f) => 
      if(x == oldx) { IExists(newx,renameFormula(oldx,newx,f)) }
      else { IExists(oldx,renameFormula(oldx,newx,f)) }
      
    case IForall(x,f) =>  
      if(x == oldx) { IForall(newx,renameFormula(oldx,newx,f)) }
      else { IForall(oldx,renameFormula(oldx,newx,f)) }
      
    case IEqual(t1,t2) => IEqual(renameTerm(oldx,newx,t1),renameTerm(oldx,newx,t2))
    case ILess(t1,t2)  => ILess(renameTerm(oldx,newx,t1), renameTerm(oldx,newx,t2))
    case IAnd(f1,f2)   => IAnd(renameFormula(oldx,newx,f1), renameFormula(oldx,newx,f2))
    case IOr(f1,f2)    => IOr(renameFormula(oldx,newx,f1), renameFormula(oldx,newx,f2))
    case INot(f)       => INot(renameFormula(oldx,newx,f))
    case ITrue()       => f
    case IFalse()      => f
  }
  
  
  def renameTerm(oldx: String, newx: String, t: Term): Term = t match {
    case IVar(y) if y == oldx => IVar(newx)
    case IVar(y) if y != oldx => t
    case IPlus(t1,t2)         => IPlus(renameTerm(oldx,newx,t1),renameTerm(oldx,newx,t2))
    case IMinus(t1,t2)        => IMinus(renameTerm(oldx,newx,t1),renameTerm(oldx,newx,t2))
    case IProd(k,t)           => IProd(k,renameTerm(oldx,newx,t))
    case IConst(_)            => t
  } 
  
  def FV(y: String ,s: Term): Boolean = s match {
    case IVar(x)       => x == y
    case IPlus(t1,t2)  => FV(y,t1) || FV(y,t2)
    case IMinus(t1,t2) => FV(y,t1) || FV(y,t2)
    case IProd(k,t)    => FV(y,t)
    case IConst(_)     => false
  }
}


/** =================================================
 *           Weakest Precondition Generator
 *  =================================================
 */

object Wp {
  
   def apply(s: IGuard, q: Form): Form = s match {
     /**wp(Q, x=t) = Q[x:=t]*/
     case IAssign(x, t) => Substitution(x,t,q)
     /**wp(Q, assume F) = F => Q*/
     case IAssume(f) => IOr(INot(f),q)
     /**wp(Q, assert F) = F & Q*/
     case IAssert(f) => IAnd(f,q)
     /**wp(Q, havoc(x)) = ALL x.Q  (or introduce a fresh variable)*/
     case IHavoc(vars) => havoc2formula(q,vars)
     /**wp(Q, c1 ; c2) = wp(wp(Q,c2),c1)*/
     case ISequence(s1,s2) => apply(s1,apply(s2,q))
     
     case IWhile(cond,inv,block) => 
       apply(ISequence(IAssert(inv),
                       ISequence(IHavoc(lookupIVars(block)),
                                 ISequence(IAssume(inv), IIf(cond, 
                                                             ISequence(block,ISequence(IAssert(inv),
                                                                             IAssume(IFalse())))
                                                             ,
                                                             IAssume(ITrue())))))
             ,
             q)
     
     /** if (f) c1 c2 <=> (assume(f);c1) [] (assume(�f);c2)
         As wp(Q,c1 [] c2) = wp(Q,c1) & wp(Q,c2) */
     case IIf(cond,then,elses) =>  
       IAnd(
         apply(ISequence(IAssume(cond),then),
               q)
         ,
         apply(ISequence(IAssume(INot(cond)),elses),
               q)
         )
     
  }
   

  def havoc2formula(q: Form, xs: Seq[IVar]): Form = 
    if(xs.isEmpty) { q }
    else { havoc2formula(IForall(xs.headOption.get.name,q),xs.drop(1)) }
  
  
  
  def lookupIVars(instr: IGuard): Seq[IVar] = instr match {
      case IAssign(x,t)           => List(IVar(x))
      case IHavoc(vars)           => vars
      case ISequence(s1,s2)       => lookupIVars(s1).concat(lookupIVars(s2))
      case IIf(cond,then,elses)   => lookupIVars(then).concat(this.lookupIVars(elses))
      case IWhile(cond,inv,block) => lookupIVars(block)
      case IAssume(_)             => List()
      case IAssert(_)             => List()
    }
  

}

        
object VerificationConditionGenerator extends Application {

  /**
   * Program:
   *
   * x = 0;
   * y = x + 3;
   * havoc(x);
   * assert (y=3);
   *
   * Test: Wp(Program,true) held a valid formula
   */
  assert(Wp( 
           ISequence(IAssign("x",IConst(0)),
           ISequence(IAssign("y",IPlus(IVar("x"),IConst(3))), 
           ISequence(IHavoc(List(IVar("x"))),
                    IAssert(IEqual(IVar("y"),IConst(3)))))
           ),
           ITrue()
       )
       ==
       IForall("x1",IAnd(IEqual(IPlus(IConst(0),IConst(3)),IConst(3)),ITrue()))
  )

}
