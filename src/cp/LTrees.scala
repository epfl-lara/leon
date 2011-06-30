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
  class LStream[T](val constraint: (L[T]) => Constraint[T]) extends scala.collection.generic.FilterMonadic[L[T], Traversable[L[T]]] {

    import ConstraintSolving.GlobalContext
    private var guards: Map[Seq[Identifier],Identifier] = Map.empty
    private var previouslyReturned: Seq[Seq[Identifier]] = Seq.empty

    private var forcedQueue: Seq[Seq[Identifier]] = Seq.empty

    // we don't have this until we first instantiate a constraint
    private var convertingFunction: (Seq[Expr]) => T = null

    def convert(s: Seq[Expr]): T = convertingFunction(s)

    def enqueueAsForced(ids: Seq[Identifier], values: Seq[Expr]): Unit = {
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

      // do it first for enumeration of one L var:
      assert(newConsts.size == 1)
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

    private def underlyingStream(): Stream[L[T]] = {

      // set of tricks to overcome circular dependency between creation of L's
      // and Constraints

      // currently works for only LStreams generating one L
      val placeHolders = Seq(FreshIdentifier("placeholder", true).setType(BottomType))
      val candidateL = new L[T](this, placeHolders)
      val instantiatedCnstr = constraint(candidateL)

      // now that we have a Constraint, we can perform some actions such as:
      GlobalContext.initializeIfNeeded(instantiatedCnstr.program)
      convertingFunction = instantiatedCnstr.convertingFunction

      val (newConsts, newExpr) = combineConstraint(instantiatedCnstr)
      val typedPlaceHolders = (newConsts zip placeHolders) map {
        case (cst, ph) => FreshIdentifier("fresh", true).setType(cst.getType)
      }
      // println("types : " + typedPlaceHolders.map(_.getType))
      val subst1 = ((newConsts map (Variable(_))) zip (typedPlaceHolders map (Variable(_)))).toMap
      val subst2 = ((placeHolders map (Variable(_))) zip (typedPlaceHolders map (Variable(_)))).toMap
      val replacedExpr = replace(subst1 ++ subst2, newExpr)

      if (isStillSat(typedPlaceHolders, replacedExpr)) {
          Stream.cons(new L[T](this, typedPlaceHolders), underlyingStream())
      } else {
          Stream.empty
      }
    }

    def flatMap [B, That] (f: (L[T]) ⇒ GenTraversableOnce[B])(implicit bf: CanBuildFrom[Traversable[L[T]], B, That]): That = {
      underlyingStream().flatMap(f)
    }

    def foreach [U] (f: (L[T]) ⇒ U): Unit = {
      underlyingStream().foreach(f)
    }

    def map [B, That] (f: (L[T]) ⇒ B)(implicit bf: CanBuildFrom[Traversable[L[T]], B, That]): That = {
      underlyingStream().map(f)
    }

    def withFilter (p: (L[T]) ⇒ Boolean): FilterMonadic[L[T], Traversable[L[T]]] = {
      underlyingStream().withFilter(p)
    }

    def withFilter2(p: (L[T]) => Constraint[T]): LStream[T] = {
      new LStream[T]((l: L[T]) => this.constraint(l).asInstanceOf[Constraint1[T]] && p(l).asInstanceOf[Constraint1[T]])
    }
  }

  implicit def force[T](l : L[T]): T = {
    l.force()
  }

  /* L for Lazy, L for Logic */
  object L {
    def unapply(l: L[_]): Option[Seq[Identifier]] = {
      if (l == null) None else Some(l.ids)
    }
  }

  class L[T](lStream: LStream[T], val ids: Seq[Identifier]) extends {
    import ConstraintSolving.GlobalContext

    var cache: Option[T] = None

    def force(): T = cache match {
      case Some(value) => value
      case None =>
        val model = GlobalContext.findValues(ids)
        val toRet = lStream.convert(model)
        lStream.enqueueAsForced(ids, model)
        cache = Some(toRet)
        toRet
    }
  }
}
