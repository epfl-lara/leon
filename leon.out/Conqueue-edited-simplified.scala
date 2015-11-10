package lazybenchmarks
import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.lang.synthesis._
import ConcTrees._
import ConQ._
import Conqueue._

object ConcTrees {
  abstract class Conc[T] { 
     def isEmpty : Boolean = this == Empty[T]()
  
	  def level : BigInt =  {
	    this match {
	      case Empty() =>
		BigInt(0)
	      case Single(x) =>
		BigInt(0)
	      case CC(l, r) =>
		BigInt(1) + max(l.level, r.level)
	    }
	  } ensuring {
	    (x$1 : BigInt) => x$1 >= BigInt(0)
	  }
  }
  
  case class Empty[T]() extends Conc[T]
  
  case class Single[T](x : T) extends Conc[T]
  
  case class CC[T](left : Conc[T], right : Conc[T]) extends Conc[T]
  
  def max(x : BigInt, y : BigInt): BigInt = if (x >= y) {
    x
  } else {
    y
  }
  
  def abs(x : BigInt): BigInt = if (x < BigInt(0)) {
    -x
  } else {
    x
  }
}

object Conqueue {
  abstract class ConQ[T] { 
    def isSpine : Boolean = this match {
	    case Spine(_, _) =>
	      true
	    case _ =>
	      false
	  }
  def isTip : Boolean = !this.isSpine
  }
  
  case class Tip[T](t : Conc[T]) extends ConQ[T]
  
  case class Spine[T](head : Conc[T], rear : LazyConQ[T]) extends ConQ[T]
  
  abstract class Scheds[T]
  
  case class Cons[T](h : LazyConQ[T], tail : Scheds[T]) extends Scheds[T]
  
  case class Nil[T]() extends Scheds[T]
  
  case class Wrapper[T](queue : LazyConQ[T], schedule : Scheds[T]) {
	def valid(st : Set[LazyConQ[T]]): Boolean = zeroPreceedsLazy[T](this.queue, st) && schedulesProperty(this.queue, this.schedule, st)
  } 
  
def zeroPreceedsLazy[T](q : LazyConQ[T], st : Set[LazyConQ[T]]): Boolean = {
  if (st.contains(q)) {
    evalLazyConQS[T](q) match {
      case Spine(Empty(), rear10) =>
        true
      case Spine(h, rear11) =>
        zeroPreceedsLazy[T](rear11, st)
      case Tip(_) =>
        true
    }
  } else {
    false
  } 
} /*ensuring { res => 
  (!zeroPreceedsLazy(firstUnevaluated(q, st), st) || res) && 
  (res || !st.contains(q) || {
    val x = firstUnevaluated(q, st)
    val (r, nst) = evalLazyConQ(x, st)     
    r match {
	case Spine(Empty(), _) => true
	case Tip(_) => true
	case _ => false
    }
    //zeroPreceedsLazy[T](q, nst) 
  })
}*/

	def zeroPredLazyMonotone[T](st1 : Set[LazyConQ[T]], st2: Set[LazyConQ[T]], q: LazyConQ[T]) : Boolean = {
	  require(st1.subsetOf(st2) && zeroPreceedsLazy(q, st1))
	  zeroPreceedsLazy(q, st2) && 
	  //induction scheme 
	  (evalLazyConQS[T](q) match {
	      case Spine(Empty(), _) =>
		true
	      case Spine(h, rear) =>
		zeroPredLazyMonotone(st1, st2, rear)
	      case Tip(_) =>
		true
	    })
	} holds

  def weakZeroPreceedsLazy[T](q : LazyConQ[T], st : Set[LazyConQ[T]]): Boolean = {  
    evalLazyConQS[T](q) match {
      case Spine(Empty(), rear10) =>
        true
      case Spine(h, rear11) =>
        zeroPreceedsLazy[T](rear11, st)
      case Tip(_) =>
        true
    }} 
  
  @library   
  def streamLemma[T](l : LazyConQ[T], st : Set[LazyConQ[T]]): Boolean =  {
    st.contains(l) || (evalLazyConQS[T](l) match {
      case Spine(_, tail14) =>
        l != tail14 && !st.contains(tail14)
      case _ =>
        true
    })
  } ensuring {
    (holds : Boolean) => holds
  }
  
  def firstUnevaluated[T](l : LazyConQ[T], st : Set[LazyConQ[T]]): LazyConQ[T] =  {
    if (st.contains(l)) {
      evalLazyConQS[T](l) match {
        case Spine(_, tail15) =>
          firstUnevaluated[T](tail15, st)
        case _ =>
          l
      }
    } else {
      l
    }
  } ensuring {
    (res65 : LazyConQ[T]) => {
      val dres4 = evalLazyConQ[T](res65, st)
      (evalLazyConQS[T](res65).isTip || !st.contains(res65)) && streamLemma[T](res65, st) && (dres4._1 match {
        case Spine(_, tail16) =>
          ((firstUnevaluated[T](l, dres4._2) == tail16), dres4._2)
        case _ =>
          (true, dres4._2)
      })._1
    }
  }
  
  def schedulesProperty[T](q : LazyConQ[T], schs : Scheds[T], st : Set[LazyConQ[T]]): Boolean = {
	  schs match {    
	    case Cons(head5, tail) =>  	
	      evalLazyConQS[T](head5).isSpine && firstUnevaluated[T](q, st) == head5 && schedulesProperty[T](pushUntilZero[T](head5), tail, st) && 
		weakZeroPreceedsLazy(head5, st)    
	    case Nil() => true	     
	  }
  }
  
  def pushUntilZero[T](q : LazyConQ[T]): LazyConQ[T] = evalLazyConQS[T](q) match {
    case Spine(Empty(), rear12) =>
      pushUntilZero[T](rear12)
    case Spine(h, rear13) =>
      rear13
    case Tip(_) =>
      q
  }
  
  def pushLeft[T](ys : Single[T], xs : LazyConQ[T], st : Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    require(zeroPreceedsLazy[T](xs, st) && ys.isInstanceOf[Single[T]])
    val dres5 = evalLazyConQ[T](xs, st)
    dres5._1 match {
      case Tip(CC(_, _)) =>
        (Spine[T](ys, xs), dres5._2)
      case Tip(Empty()) =>
        (Tip[T](ys), dres5._2)
      case Tip(t @ Single(_)) =>
        (Tip[T](CC[T](ys, t)), dres5._2)
      case s @ Spine(Empty(), rear) =>
	(Spine[T](ys, rear), dres5._2) // in this case firstUnevaluated[T](rear, st) == firstUnevaluated[T](xs, st)
      case s @ Spine(_, _) =>
        pushLeftLazy[T](ys, xs, dres5._2)
    }
  } ensuring { res => 
	true
    }

  def dummyFun[T]() =  ???[(ConQ[T], Set[LazyConQ[T]])]

  @library
  def pushLeftLazyUI[T](ys : Conc[T], xs : LazyConQ[T], st : Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
	dummyFun()
  } ensuring(res => res._2 == st && (res._1 match {
          case Spine(Empty(), rear) =>
	      (evalLazyConQS[T](rear).isSpine && !st.contains(rear)) &&
              (firstUnevaluated[T](pushUntilZero[T](rear), st) == firstUnevaluated[T](xs, st) ||
				      evalLazyConQS[T](firstUnevaluated[T](xs, st)).isTip) &&
			//evalLazyConQS[T](firstUnevaluated[T](pushUntilZero[T](rear), st)).isTip)
	      weakZeroPreceedsLazy(rear, st)
          case _ => false	      
            //firstUnevaluated[T](rear, st) == firstUnevaluated[T](xs, st) 		
        }))
  
  //@library
  def pushLeftLazy[T](ys : Conc[T], xs : LazyConQ[T], st : Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) =  {
    require(!ys.isEmpty && zeroPreceedsLazy[T](xs, st) && 
		(evalLazyConQS[T](xs) match { 
		  case Spine(h, _) => h != Empty[T]()
		  case _ => false
		}))
    val dres = evalLazyConQ[T](xs, st)
    dres._1 match {
      case Spine(head, rear15) =>
        val carry = CC[T](head, ys)
        val dres2 = evalLazyConQ[T](rear15, dres._2)
        dres2._1 match {
	  case s @ Spine(Empty(), _) =>
	    (Spine[T](Empty[T](), newConQ(Lazyarg1[T](Spine(carry, rear15)), dres2._2)), dres2._2)
          case s @ Spine(_, _) =>
            (Spine[T](Empty[T](), newConQ[T](PushLeftLazy[T](carry, rear15), dres2._2)), dres2._2)
          case t @ Tip(tree) =>
	    if (tree.level > carry.level) { // can this happen ? this means tree is of level at least two greater than rear ?
              val x : ConQ[T] = t
              val y : ConQ[T] = Spine[T](carry, newConQ[T](Lazyarg1[T](x), dres._2))
              (Spine[T](Empty[T](), newConQ[T](Lazyarg1[T](y), dres2._2)), dres2._2)
            } else {// here tree level and carry level are equal
              val x : ConQ[T] = Tip[T](CC[T](tree, carry))
              val y : ConQ[T] = Spine[T](Empty[T](), newConQ[T](Lazyarg1[T](x), dres._2))
              (Spine[T](Empty[T](), newConQ[T](Lazyarg1[T](y), dres2._2)), dres2._2)	
            }
        }
    }
  } ensuring {
    (res66 : (Spine[T], Set[LazyConQ[T]])) => (res66._2 == st) && (res66._1 match {
      case Spine(Empty(), rear) =>
	     val (rearval, _) = evalLazyConQ[T](rear, st) // this is necessary to assert properties on the state in the recurisve invocation
	     rearval.isSpine && !st.contains(rear) && 	     
	    (evalLazyConQS[T](firstUnevaluated[T](xs, st)).isTip || 
		//evalLazyConQS[T](firstUnevaluated[T](pushUntilZero[T](rear), st)).isTip ||
		firstUnevaluated[T](pushUntilZero[T](rear), st) == firstUnevaluated[T](xs, st)) &&
		weakZeroPreceedsLazy(rear, st)
      case _ =>
	false        
    })
  }
  
  /*def PushLeftLazypushLeftLazyLem[T](rear15 : LazyConQ[T], head : Conc[T], dres : (ConQ[T], Set[LazyConQ[T]]), st : Set[LazyConQ[T]], xs : LazyConQ[T], s : Spine[T], dres : (ConQ[T], Set[LazyConQ[T]]), carry : CC[T], ys : Conc[T]): Boolean =  {
    (!ys.isEmpty && zeroPreceedsLazy[T](xs, st) && evalLazyConQS[T](xs).isSpine && dres == evalLazyConQ[T](xs, st) && (!dres._1.isInstanceOf[Spine[T]] || !dres._1.head.isInstanceOf[Empty[T]]) && dres._1.isInstanceOf[Spine[T]] && head == dres._1.head && rear15 == dres._1.rear && carry == CC[T](head, ys) && dres == evalLazyConQ[T](rear15, dres._2) && (!dres._1.isInstanceOf[Spine[T]] || !dres._1.head.isInstanceOf[Empty[T]]) && dres._1.isInstanceOf[Spine[T]] && s == dres._1) ==> (!carry.isEmpty && zeroPreceedsLazy[T](rear15, dres._2) && evalLazyConQS[T](rear15).isSpine)
  } ensuring {
    (holds : Boolean) => holds
  }*/

  def streamContains[T](l: LazyConQ[T], newl: LazyConQ[T]) : Boolean = {
    (l == newl) || (evalLazyConQS[T](l) match {
       case Spine(_ , tail) => 
          streamContains(tail, newl)
        case _ => false
     })
  }
  
  // monotonicity of fune
  def funeMonotone[T](st1 : Set[LazyConQ[T]], st2 : Set[LazyConQ[T]], l : LazyConQ[T], newl: LazyConQ[T]) : Boolean = {   
    require(st2 == st1 ++ Set(newl) && 
      !streamContains(l, newl))
    (firstUnevaluated(l, st1) == firstUnevaluated(l, st2)) && //property
	 //induction scheme
      (evalLazyConQS[T](l) match {
        case Spine(_, tail) =>	  
          	funeMonotone(st1, st2, tail, newl)
        case _ =>          
		        true
      })    
  } holds

  // isConcrete monotonicity
  // def concreteMonotone[T](st1 : Set[LazyConQ[T]], st2 : Set[LazyConQ[T]], l : LazyConQ[T]) : Boolean = {   
  //   ((isConcrete(l, st1) && st1.subsetOf(st2)) ==> isConcrete(l, st2)) && {
  //     // induction scheme
  //     evalLazyConQS[T](l) match {
  //       case Spine(_, tail) =>
  //         concreteMonotone[T](st1, st2, tail)
  //       case _ =>
  //         true
  //     }
  //   }
  // } holds

  @library // To be proven
  def schedMonotone[T](st1: Set[LazyConQ[T]], st2 : Set[LazyConQ[T]], scheds: Scheds[T], l : LazyConQ[T], newl: LazyConQ[T]) : Boolean = {  
    require((st2 == st1 ++ Set(newl)) && 
      !streamContains(l, newl) && // newl is not contained in 'l'
      schedulesProperty(l, scheds, st1)
      ) 
    //concreteMonotone(st1, st2, l) && 
    zeroPredLazyMonotone(st1, st2, l) &&
    funeMonotone(st1, st2, l, newl) &&   //instantiations   
       schedulesProperty(l, scheds, st2) &&  //property
       //induction scheme
       (scheds match {
          case Cons(head, tail) => 
            schedMonotone(st1, st2, tail, pushUntilZero(head), newl)
          case Nil() => true
        })      
  } holds
  
  @library
  def newLazyCons[T](q: ConQ[T], st : Set[LazyConQ[T]]) : LazyConQ[T] = {
    newConQ[T](Lazyarg1(q), st)
  } ensuring(r => q match {
      case Spine(_, rear) =>
        !streamContains(rear, r)
        case _ => true          
    })

  //@library
  def pushLeftWrapper[T](ys : Single[T], w : Wrapper[T], st : Set[LazyConQ[T]]) = { 
    require(w.valid(st) && ys.isInstanceOf[Single[T]])    
    val (nq, nst) = pushLeft[T](ys, w.queue, st)    
    val nsched = nq match {
      case Spine(Empty(), rear18) =>
        Cons[T](rear18, w.schedule)
      case Spine(_, _) =>
        w.schedule
      case _ => Nil[T]() // if 'nq' is Tip don't add it to schedule
    }           
    val lq = newLazyCons(nq, nst)
    val (_, rst) = evalLazyConQ(lq, nst)
    (lq, nsched, rst)
  } ensuring {res =>  
    //zeroPreceedsLazy(res._1, res._3)    
    schedulesProperty(res._1, res._2, res._3) &&     
    // instantiations
     (evalLazyConQS(res._1) match { 
          case Spine(_, rear) =>
            schedMonotone(st, res._3, res._2, rear, res._1)
          case _ => true
     })
  }

  @library
  def dummyAxiom[T](l: LazyConQ[T], nl: LazyConQ[T]) : Boolean = {
    !streamContains(l, nl)
  } holds

  def funeCompose[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], q : LazyConQ[T]) : Boolean = {
    require(st1.subsetOf(st2))
    (firstUnevaluated(firstUnevaluated(q, st1), st2) == firstUnevaluated(q, st2)) && //property
    //induction scheme
      (evalLazyConQS[T](q) match {
        case Spine(_, tail) =>    
            funeCompose(st1, st2, tail)
        case _ =>          
            true
      }) 
  } holds
  
  def funeZeroProp[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], q : LazyConQ[T]) : Boolean = {
    require(st1.subsetOf(st2) && {
 	val x = firstUnevaluated(q, st1)
	st2.contains(x) && weakZeroPreceedsLazy(x, st1)
     })
    zeroPreceedsLazy(q, st2) && //property
    //induction scheme
      (evalLazyConQS[T](q) match {
        case Spine(h, tail) =>    
 	    (if(st1.contains(q))
                 funeZeroProp(st1, st2, tail)
	     else true) && 
	     (if(h != Empty[T]())
		     zeroPredLazyMonotone(st1, st2, tail)	
		else true)
        case _ =>          
            true
      }) 
  } holds
  
  //@library
  def Pay[T](q : LazyConQ[T], scheds : Scheds[T], st : Set[LazyConQ[T]]): (Scheds[T], Set[LazyConQ[T]]) = {
    require(schedulesProperty(q, scheds, st) && st.contains(q))    
    val (nschs, rst) = scheds match {
      case c @ Cons(head, rest) =>
        val (headval, st2) = evalLazyConQ(head, st)
        (headval match {
          case Spine(Empty(), rear) =>
            evalLazyConQS(rear) match{ // note: here we are ignoring tip
              case Spine(_, _) => 
                Cons(rear, rest) 
              case _ => rest
	    }
          case _ =>
            rest  // in this case: firstUnevaluated[T](rear, st) == rhead  && firstUnevaluated[T](q, res._2) == rhead by funeCompose                                                
        }, st2)
      case Nil() =>        
        (scheds, st)
    }
    (nschs, rst)
  } ensuring {res =>
     schedulesProperty(q, res._1, res._2) &&      
     // instantiations (relating rhead and head)
     funeCompose(st, res._2, q) && 
     (res._1 match {
      case Cons(rhead, rtail) =>
	  // establishing the zeroPreceedsLazy Property (on this case)
	  
          (scheds match {
              case Cons(head, rest) =>                 
                dummyAxiom(pushUntilZero(rhead), head) &&   
		schedMonotone(st, res._2, rtail, pushUntilZero(rhead), head)
                /*(evalLazyConQS(firstUnevaluated(q, st)).isTip ||		            		
            		( (evalLazyConQS(head) match {
            			case Spine(Empty(), rear) => 
				   //firstUnevaluated(q, res._2) == rhead && 
				   //schedulesProperty(pushUntilZero(rhead), rtail, st)      			           
            			case Spine(_, rear) => 
				  //firstUnevaluated(rear, st) == rhead &&                                        		  
				  //schedulesProperty(pushUntilZero(head), res._1, st) &&
				  //schedulesProperty(pushUntilZero(rhead), rtail, st) 				  
	                          schedMonotone(st, res._2, rtail, pushUntilZero(rhead), head)
            		}))
                )*/
              case _ => true 		
          })        
      case _ => true          
     }) //&&
     // zeroPreceedsLazy(q, res._2) && 
     // // instantiations for zeroPreceedsLazy
     // zeroPredLazyMonotone(st, res._2, q)     
  }

  /*def pushLeftAndPay[T](ys : Single[T], w : Wrapper[T], st : Set[LazyConQ[T]]): (Wrapper[T], Set[LazyConQ[T]]) = {
    require(w.valid(st) && ys.isInstanceOf[Single[T]])
    val (q, scheds, nst) =  pushLeftWrapper(ys, w, st)
    val (nscheds, fst) = Pay(q, scheds, nst)
    (Wrapper(q, nscheds), fst)
  } ensuring {res => res._1.valid(res._2) }*/
  
  def lazyarg1[T](x : ConQ[T]): ConQ[T] = x
}

object ConQ {  
  
  abstract class LazyConQ[T1]
  
  case class Lazyarg1[T](x : ConQ[T]) extends LazyConQ[T]
  
  case class PushLeftLazy[T](ys : Conc[T], xs : LazyConQ[T]) extends LazyConQ[T]
  
  @library
  def newConQ[T1](cc : LazyConQ[T1], st : Set[LazyConQ[T1]]): LazyConQ[T1] =  {
    cc
  } ensuring {
    (res : LazyConQ[T1]) => !st.contains(res)
  }
  
  @library
  def evalLazyConQ[T](cl : LazyConQ[T], st : Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) =  {
    cl match {
      case t : Lazyarg1[T] =>
        (t.x, (st ++ Set[LazyConQ[T]](t)))
      case t : PushLeftLazy[T] =>
	val plres = pushLeftLazyUI[T](t.ys, t.xs, uiState())._1
	val plst = pushLeftLazyUI[T](t.ys, t.xs, st)._2
        (plres, (plst ++ Set[LazyConQ[T]](t)))
    }
  } ensuring {
    (res : (ConQ[T], Set[LazyConQ[T]])) => (cl match {
      case t : Lazyarg1[T] =>
	//true       
	res._1 match {
	 case Spine(_, r) => weakZeroPreceedsLazy(r, st)  // need to be autogen
	 case _ => true
        }
      case t : PushLeftLazy[T] =>        
	true
     })
  }

  def uiState[T]() : Set[LazyConQ[T]] = ???[Set[LazyConQ[T]]]
  
  def evalLazyConQS[T](cl : LazyConQ[T]): ConQ[T] = evalLazyConQ[T](cl, uiState())._1
 
}
