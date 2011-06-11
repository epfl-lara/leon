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
  class LStream[T](val constraint: Constraint[T]) extends scala.collection.generic.FilterMonadic[L[T], Traversable[L[T]]] {

    import ConstraintSolving.GlobalContext
    GlobalContext.initializeIfNeeded(constraint.program)

    private var liveSet: Set[Identifier] = Set.empty
    private var deadSet: Set[Identifier] = Set.empty

    private var guards: Map[Seq[Identifier],Identifier] = Map.empty

    private var previouslyReturned: Seq[Seq[Identifier]] = Seq.empty

    def markAsForced(ids: Seq[Identifier], values: Seq[Expr]): Unit = {
      val guard = guards(ids)

      // remove from live set
      assert(liveSet.contains(guard))
      liveSet = liveSet - guard
      deadSet = deadSet + guard

      // assert not live
      val noMoreLive = Not(Variable(guard))
      // assert value
      val haveValues = And((ids zip values) map {
        case (i, v) => Equals(Variable(i), v)
      })

      if (! GlobalContext.assertConstraint(And(noMoreLive, haveValues)))
        throw new Exception("assertion of dead literals and forced values returned UNSAT")
    }

    private def isStillSat(): Option[Seq[Identifier]] = {
      val (newConsts, newExpr) = combineConstraint(constraint)

      // do it first for enumeration of one L var:
      assert(newConsts.size == 1)
      val newGuard = FreshIdentifier("live", true).setType(BooleanType)

      liveSet = liveSet + newGuard
      guards = guards + (newConsts -> newGuard)

      // for all previous sequences of returned identifiers, assert that the new sequence is distinct from them
      val differentFromPrevious = And(previouslyReturned map (ps => Not(And((ps zip newConsts) map { case (p, n) => Equals(Variable(p), Variable(n)) }))))
      val toAssert = Implies(Variable(newGuard), And(newExpr, differentFromPrevious))
      if (GlobalContext.checkAssumptions(toAssert, liveSet map (Variable(_)))) {
        previouslyReturned = newConsts +: previouslyReturned
        assert(GlobalContext.assertConstraint(differentFromPrevious))
        Some(newConsts)
      } else {
        None
      }
    }

    private def underlyingStream(): Stream[L[T]] = {
      isStillSat() match {
        case Some(newIDs) =>
          Stream.cons(new L[T](this, newIDs), underlyingStream())
        case None =>
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
      throw new Exception()
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

    // private def modelNegation(vs: Seq[Expr]): Expr = {
    //   Not(And(((ids map (i => Variable(i))) zip vs) map { case (i, v) => Equals(i, v) }))
    // }

    var cache: Option[T] = None

    def force(): T = cache match {
      case Some(value) => value
      case None =>
        val model = GlobalContext.findValues(ids)
        val toRet = lStream.constraint.convertingFunction(model)
        lStream.markAsForced(ids, model)
        cache = Some(toRet)
        toRet
    }
  }
}
