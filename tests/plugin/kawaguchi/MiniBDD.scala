package plugin.kawaguchi

/* Example from paper "Type-based Data Structure Verification"
 * http://pho.ucsd.edu/liquid/demo/index2.php */

import funcheck.lib.Specs._

object MiniBDD {

  @generator
  sealed abstract class BDD
  case class Node(v: Int, low: BDD, high: BDD) extends BDD
  case class Zero() extends BDD
  case class One() extends BDD
  
  @generator
  sealed class Op
  case class And() extends Op
  case class Or() extends Op
  case class Imp() extends Op
  case class Any(f: (Boolean,Boolean) => Boolean) extends Op
  
  def myfail: BDD = {
    assert(false)
    null
  }
  
  def bdd2int(b: BDD): Int = b match {
    case Zero() | One() => 1000
    case Node(v,_,_) => v
  }
  
  def utag(b: BDD): Int = b match {
    case Zero() => 0
    case One() => 1
    case Node(v,_,_) => v
  }
  
  def low(b: BDD): BDD = b match {
    case Node(_,l,_) => l
    case _ => myfail
  }
  
  def high(b: BDD): BDD = b match {
    case Node(_,_,h) => h
    case _ => myfail
  }
  
  
  val zero = Zero()
  val one = One()
  
  def of_bool(b: Boolean): BDD = if(b) one else zero
  
  def check(b: BDD): Boolean = b match {
    case Zero() | One() => true
    case Node(v,l,h) => 
      (v < bdd2int(l)) &&
      (v < bdd2int(h)) &&
      check(l) && check(h)
  }
  
  def mk(x: Int, low: BDD, high: BDD) = 
    if(low == high) low else Node(x,low,high)
  
  def empty = Map.empty[BDD,BDD]
  def empty2 = Map.empty[(BDD,BDD),BDD]
  
  def mk_not(x: BDD): BDD = {
    val cache = empty
    assert(check(x))
    
    def mk_not_rec(cache: Map[BDD,BDD], x: BDD): (Map[BDD,BDD],BDD) = {
      cache.get(x) match {
        case Some(x) => 
          (cache,x)
        case None => {
          val (table,res) = {
            x match {
              case Zero() => (cache,one)
              case One() => (cache,zero)
              case Node(v,l,h) =>
                val (cachel,ll) = mk_not_rec(cache,l)
                val (cacheh, hh) = mk_not_rec(cache,h)
                (cachel ++ cacheh, mk(v,ll,hh))
            }
          }
          
          (table + ((x -> res)),res)
        }
      }
    }
    
    val (_,rv) = mk_not_rec(cache, x)
    assert(check(rv))
    rv
  }
  
  def apply_op(op: Op, b1: Boolean, b2: Boolean): Boolean = op match {
    case And() => b1 && b2
    case Or() => b1 || b2
    case Imp() => !b1 || b2
    case Any(f) => f(b1,b2)
  }
  
  def gapply(op: Op): (BDD,BDD) => BDD = {
    val op_z_z = of_bool(apply_op(op, false,false))
    val op_z_o = of_bool(apply_op(op, false,true))
    val op_o_z = of_bool(apply_op(op, true,false))
    val op_o_o = of_bool(apply_op(op, true,true))
    
    (b1: BDD, b2: BDD) => {
       val cache = empty2
       
       def app(cache: Map[(BDD,BDD),BDD], u1: BDD, u2: BDD): (Map[(BDD,BDD),BDD], BDD) = { 
         def default(res: BDD) = (cache,res)
         op match {
           case And() =>
             if(u1 == u2) default(u1)
             else if(u1 == zero || u2 == zero) default(zero)
             else if(u1 == one) default(u2)
             else if(u2 == one) default(u1)
             else app_gen(cache, u1,u2)
           
           case Or() =>
             if(u1 == u2) default(u1)
             else if(u1 == one || u2 == one) default(one)
             else if(u1 == zero) default(u2)
             else if(u2 == zero) default(u1)
             else app_gen(cache, u1,u2)
           
           case Imp() =>
             if(u1 == zero) default(one)
             else if(u1 == one) default(u2)
             else if(u2 == one) default(u1)
             else app_gen(cache, u1,u2)
         
           case Any(_) => app_gen(cache, u1,u2)
         }
       }
       
       def app_gen(cache: Map[(BDD,BDD),BDD], u1: BDD, u2: BDD): (Map[(BDD,BDD),BDD],BDD) = (u1,u2) match {
         case (Zero(),Zero()) => (cache, op_z_z)
         case (Zero(),One()) => (cache, op_z_o)
         case (One(),Zero()) => (cache, op_o_z)
         case (One(),One()) => (cache, op_o_o)
         case _ =>
           cache.get((u1,u2)) match {
             case Some(x) => (cache, x)
             case None =>
               val (cacheres, res) = {
                 val v1 = bdd2int(u1)
                 val v2 = bdd2int(u2)
                 if(v1 == v2) {
                   val (cachelow,applow) = app(cache, low(u1),low(u2))
                   val (cachehigh,apphigh) = app(cache, high(u1),high(u2))
                   (cachelow ++ cachehigh, mk(v1, applow, apphigh))
                 } else if(v1 < v2) {
                   val (cachelow,applow) = app(cache, low(u1),u2)
                   val (cachehigh,apphigh) = app(cache, high(u1),u2)
                   (cachelow ++ cachehigh, mk(v1, applow, apphigh))
                 } else {
                   val (cachelow,applow) = app(cache, u1,low(u2))
                   val (cachehigh,apphigh) = app(cache, u1,high(u2))
                   (cachelow ++ cachehigh, mk(v2, applow, apphigh))
                 }
               }
               (cacheres + (((u1,u2) -> res)), res)
           }
       }
             
       val (_,res) = app(cache, b1, b2)
       res
    
    }
  }
}
