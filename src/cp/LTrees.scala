package cp

import Terms._
import ConstraintSolving._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

import scala.collection.generic.FilterMonadic
import scala.collection.generic.CanBuildFrom
import scala.collection.GenTraversableOnce

object LTrees {
  /** Handler for converting values from Expr to Scala and reporting forced
   * values */
  trait LHandler[T] {
    val converter: Converter
    def enqueueAsForced(ids: Seq[Identifier], values: Seq[Expr]): Unit
  }

  /* Symbolic variables */
  object L {
    def unapply(l: L[_]): Option[Seq[Identifier]] = {
      if (l == null) None else Some(l.ids)
    }
  }

  class L[T](handler: LHandler[T], val ids: Seq[Identifier]) extends {
    import ConstraintSolving.GlobalContext

    var cache: Option[T] = None

    def value: T = cache match {
      case Some(value) => value
      case None =>
        val model = GlobalContext.findValues(ids)
        val toRet = handler.converter.exprSeq2scala1[T](model)
        handler.enqueueAsForced(ids, model)
        cache = Some(toRet)
        toRet
    }
  }

  trait LTuple[T] {
    /* Forces this tuple to have a value */
    def value: T
  }

  /** GENERATED CODE ***/

  class LTuple1[T1](l1: L[T1]) extends LTuple[(T1)] {
    def _1: L[T1] = l1
    def value: (T1) = (_1.value)
  }
  
  class LTuple2[T1,T2](l1: L[T1],l2: L[T2]) extends LTuple[(T1,T2)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def value: (T1,T2) = (_1.value,_2.value)
  }
  
  class LTuple3[T1,T2,T3](l1: L[T1],l2: L[T2],l3: L[T3]) extends LTuple[(T1,T2,T3)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def value: (T1,T2,T3) = (_1.value,_2.value,_3.value)
  }
  
  class LTuple4[T1,T2,T3,T4](l1: L[T1],l2: L[T2],l3: L[T3],l4: L[T4]) extends LTuple[(T1,T2,T3,T4)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def _4: L[T4] = l4
    def value: (T1,T2,T3,T4) = (_1.value,_2.value,_3.value,_4.value)
  }
  
  class LTuple5[T1,T2,T3,T4,T5](l1: L[T1],l2: L[T2],l3: L[T3],l4: L[T4],l5: L[T5]) extends LTuple[(T1,T2,T3,T4,T5)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def _4: L[T4] = l4
    def _5: L[T5] = l5
    def value: (T1,T2,T3,T4,T5) = (_1.value,_2.value,_3.value,_4.value,_5.value)
  }
  
  class LTuple6[T1,T2,T3,T4,T5,T6](l1: L[T1],l2: L[T2],l3: L[T3],l4: L[T4],l5: L[T5],l6: L[T6]) extends LTuple[(T1,T2,T3,T4,T5,T6)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def _4: L[T4] = l4
    def _5: L[T5] = l5
    def _6: L[T6] = l6
    def value: (T1,T2,T3,T4,T5,T6) = (_1.value,_2.value,_3.value,_4.value,_5.value,_6.value)
  }
  
  class LTuple7[T1,T2,T3,T4,T5,T6,T7](l1: L[T1],l2: L[T2],l3: L[T3],l4: L[T4],l5: L[T5],l6: L[T6],l7: L[T7]) extends LTuple[(T1,T2,T3,T4,T5,T6,T7)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def _4: L[T4] = l4
    def _5: L[T5] = l5
    def _6: L[T6] = l6
    def _7: L[T7] = l7
    def value: (T1,T2,T3,T4,T5,T6,T7) = (_1.value,_2.value,_3.value,_4.value,_5.value,_6.value,_7.value)
  }
  
  class LTuple8[T1,T2,T3,T4,T5,T6,T7,T8](l1: L[T1],l2: L[T2],l3: L[T3],l4: L[T4],l5: L[T5],l6: L[T6],l7: L[T7],l8: L[T8]) extends LTuple[(T1,T2,T3,T4,T5,T6,T7,T8)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def _4: L[T4] = l4
    def _5: L[T5] = l5
    def _6: L[T6] = l6
    def _7: L[T7] = l7
    def _8: L[T8] = l8
    def value: (T1,T2,T3,T4,T5,T6,T7,T8) = (_1.value,_2.value,_3.value,_4.value,_5.value,_6.value,_7.value,_8.value)
  }
  
  class LTuple9[T1,T2,T3,T4,T5,T6,T7,T8,T9](l1: L[T1],l2: L[T2],l3: L[T3],l4: L[T4],l5: L[T5],l6: L[T6],l7: L[T7],l8: L[T8],l9: L[T9]) extends LTuple[(T1,T2,T3,T4,T5,T6,T7,T8,T9)] {
    def _1: L[T1] = l1
    def _2: L[T2] = l2
    def _3: L[T3] = l3
    def _4: L[T4] = l4
    def _5: L[T5] = l5
    def _6: L[T6] = l6
    def _7: L[T7] = l7
    def _8: L[T8] = l8
    def _9: L[T9] = l9
    def value: (T1,T2,T3,T4,T5,T6,T7,T8,T9) = (_1.value,_2.value,_3.value,_4.value,_5.value,_6.value,_7.value,_8.value,_9.value)
  }
  /** END OF GENERATED CODE ***/

  def dummyL[T]: L[T] = new L[T](null, Seq(FreshIdentifier("dummy", true).setType(BottomType)))
  def dummyTuple1[T1]: Tuple1[L[T1]] = Tuple1(dummyL[T1])
  def dummyTuple2[T1,T2]: (L[T1],L[T2]) = (dummyL[T1],dummyL[T2])
  def dummyTuple3[T1,T2,T3]: (L[T1],L[T2],L[T3]) = (dummyL[T1],dummyL[T2],dummyL[T3])
  def dummyTuple4[T1,T2,T3,T4]: (L[T1],L[T2],L[T3],L[T4]) = (dummyL[T1],dummyL[T2],dummyL[T3],dummyL[T4])
  def dummyTuple5[T1,T2,T3,T4,T5]: (L[T1],L[T2],L[T3],L[T4],L[T5]) = (dummyL[T1],dummyL[T2],dummyL[T3],dummyL[T4],dummyL[T5])
  def dummyTuple6[T1,T2,T3,T4,T5,T6]: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6]) = (dummyL[T1],dummyL[T2],dummyL[T3],dummyL[T4],dummyL[T5],dummyL[T6])
  def dummyTuple7[T1,T2,T3,T4,T5,T6,T7]: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7]) = (dummyL[T1],dummyL[T2],dummyL[T3],dummyL[T4],dummyL[T5],dummyL[T6],dummyL[T7])
  def dummyTuple8[T1,T2,T3,T4,T5,T6,T7,T8]: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8]) = (dummyL[T1],dummyL[T2],dummyL[T3],dummyL[T4],dummyL[T5],dummyL[T6],dummyL[T7],dummyL[T8])
  def dummyTuple9[T1,T2,T3,T4,T5,T6,T7,T8,T9]: (L[T1],L[T2],L[T3],L[T4],L[T5],L[T6],L[T7],L[T8],L[T9]) = (dummyL[T1],dummyL[T2],dummyL[T3],dummyL[T4],dummyL[T5],dummyL[T6],dummyL[T7],dummyL[T8],dummyL[T9])

  class LIterator1[T1](val constraintGivenTuple: (L[T1]) => Constraint1[T1]) extends LIterator[T1,(L[T1])] {
    val dummyTuple: Tuple1[L[T1]] = dummyTuple1[T1]
    val constraint: Constraint[T1] = constraintGivenTuple(dummyTuple._1)

    def withFilter2(p: (L[T1]) => Constraint[T1]): LIterator1[T1] = {
      new LIterator1[T1]((l: L[T1]) => this.constraintGivenTuple(l).asInstanceOf[Constraint1[T1]] && p(l).asInstanceOf[Constraint1[T1]])
    }
  }

  class LIterator2[T1,T2](val constraintGivenTuple: ((L[T1], L[T2])) => Constraint2[T1,T2]) extends LIterator[(T1,T2),(L[T1],L[T2])] {
    val dummyTuple: (L[T1],L[T2]) = dummyTuple2[T1,T2]
    val constraint: Constraint[(T1,T2)] = constraintGivenTuple(dummyTuple)

    def withFilter2(p: ((L[T1],L[T2])) => Constraint[(T1,T2)]): LIterator2[T1,T2] = {
      new LIterator2[T1,T2]((t: (L[T1],L[T2])) => this.constraintGivenTuple(t).asInstanceOf[Constraint2[T1,T2]] && p(t).asInstanceOf[Constraint2[T1,T2]])
    }
  }

  /** A lazy iterator for symbolic variables. S denotes the Scala value type
   * (which can be a tuple) and T denotes the corresponding L tuple type. */
  abstract class LIterator[S,T] extends Iterator[T] {
    val dummyTuple: Product
    val constraint: Constraint[S]

    import ConstraintSolving.GlobalContext
    private var guards: Map[Seq[Identifier],Identifier] = Map.empty
    private var previouslyReturned: Seq[Seq[Identifier]] = Seq.empty

    private var forcedQueue: Seq[Seq[Identifier]] = Seq.empty

    // we don't have this until we first instantiate a constraint
    // private var convertingFunction: (Seq[Expr]) => T = null

    def enqueueAsForcedInStream(ids: Seq[Identifier], values: Seq[Expr]): Unit = {
      // assert value
      val haveValues = And((ids zip values) map {
        case (i, v) => Equals(Variable(i), v)
      })

      GlobalContext.enqueueAssert(haveValues)
      forcedQueue = ids +: forcedQueue
    }

    def removeGuard(ids: Seq[Identifier]): Unit = {
      val guard = guards(ids)

      // remove from live set
      assert(GlobalContext.isAlive(guard))
      GlobalContext.kill(guard)

      // assert not live
      val noMoreLive = Not(Variable(guard))

      GlobalContext.enqueueAssert(noMoreLive)
    }

    private def isStillSat(newConsts: Seq[Identifier], newExpr: Expr): Boolean = {
      
      for (ids <- forcedQueue) {
        removeGuard(ids)
      }
      forcedQueue = Seq.empty

      val newGuard = FreshIdentifier("live", true).setType(BooleanType)

      GlobalContext.addLive(newGuard)
      guards = guards + (newConsts -> newGuard)

      // for all previous sequences of returned identifiers, assert that the new sequence is distinct from them
      val differentFromPrevious = And(previouslyReturned map (ps => Not(And((ps zip newConsts) map { case (p, n) => Equals(Variable(p), Variable(n)) }))))
      val toAssert = Implies(Variable(newGuard), And(newExpr, differentFromPrevious))
      if (GlobalContext.checkAssumptions(toAssert)) {
        if (!previouslyReturned.isEmpty)
          assert(GlobalContext.assertConstraint(differentFromPrevious))
        previouslyReturned = newConsts +: previouslyReturned
        true
      } else {
        removeGuard(newConsts)
        false
      }
    }

    private def handler(): LHandler[T] = new LHandler[T] {
      val converter: Converter = constraint.converter
      def enqueueAsForced(ids: Seq[Identifier], values: Seq[Expr]): Unit =
        enqueueAsForcedInStream(ids, values)
    }

    private var underlying = underlyingStream()

    private def underlyingStream(): Stream[L[T]] = {

      // set of tricks to overcome circular dependency between creation of L's
      // and Constraints

      val placeHolders: Seq[Identifier] = (for (l <- dummyTuple.productIterator) yield {
        assert(l.isInstanceOf[L[_]])
        val castedL = l.asInstanceOf[L[_]]
        assert(castedL.ids.size == 1)
        castedL.ids.head
      }).toSeq

      // now that we have a Constraint, we can perform some actions such as:
      GlobalContext.initializeIfNeeded(constraint.program)
      // convertingFunction = constraint.convertingFunction

      val (newConsts, newExpr) = combineConstraint(constraint)
      val typedPlaceHolders = newConsts map {
        case cst => FreshIdentifier("fresh", true).setType(cst.getType)
      }
      // println("types : " + typedPlaceHolders.map(_.getType))
      val subst1 = ((newConsts map (Variable(_))) zip (typedPlaceHolders map (Variable(_)))).toMap
      val subst2 = ((placeHolders map (Variable(_))) zip (typedPlaceHolders map (Variable(_)))).toMap
      val replacedExpr = replace(subst1 ++ subst2, newExpr)

      if (isStillSat(typedPlaceHolders, replacedExpr)) {
          Stream.cons(new L[T](handler(), typedPlaceHolders), underlyingStream())
      } else {
          Stream.empty
      }
    }

    def hasNext: Boolean = !underlying.isEmpty
    def next: T = {
      val toRet = underlying.head
      underlying = underlying.tail
      // toRet
      throw new Exception()
    }

    def withFilter2(p: (T) => Constraint[S]): LIterator[S,T] /*= {
      new LIterator[T]((l: L[T]) => this.constraint(l).asInstanceOf[Constraint1[T]] && p(l).asInstanceOf[Constraint1[T]])
    }*/
  }

}
