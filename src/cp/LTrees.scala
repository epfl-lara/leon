package cp

import Terms._
import ConstraintSolving._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

object LTrees {
  class LStream[T](val constraint: Constraint[T]) extends scala.collection.generic.FilterMonadic[L[T], Traversable[L[T]]] {
    import scala.collection._
    import scala.collection.generic._

    val (consts, exprWithConsts) = combineConstraint(constraint)
    private var assertQueue: Seq[Expr] = Seq.empty
    private var shouldCleanup = false

    // assert the associated constraint
    import ConstraintSolving.GlobalContext
    GlobalContext.initializeIfNeeded(constraint.program)
    if (!GlobalContext.isActive()) {
      GlobalContext.activate()
      shouldCleanup = true
    }
    GlobalContext.assertConstraint(exprWithConsts)

    def enqueue(expr: Expr): Unit = {
      assertQueue = expr +: assertQueue
    }

    def assertEnqueued(): Unit = {
      if (!assertQueue.isEmpty) {
        GlobalContext.assertConstraint(And(assertQueue))
        assertQueue = Seq.empty
      }
    }

    def isStillSat(): Boolean = {
      assertEnqueued()
      GlobalContext.assertModelNegation()
      GlobalContext.checkConsistency()
    }

    private def lStream(): Stream[L[T]] = {
      if (isStillSat())
        Stream.cons(new L[T](this, consts), lStream())
      else {
        if (shouldCleanup) {
          GlobalContext.restart()
          GlobalContext.deactivate()
        }
        Stream.empty
      }
    }

    def flatMap [B, That] (f: (L[T]) ⇒ GenTraversableOnce[B])(implicit bf: CanBuildFrom[Traversable[L[T]], B, That]): That = {
      lStream().flatMap(f)
    }

    def foreach [U] (f: (L[T]) ⇒ U): Unit = {
      lStream().foreach(f)
    }

    def map [B, That] (f: (L[T]) ⇒ B)(implicit bf: CanBuildFrom[Traversable[L[T]], B, That]): That = {
      lStream().map(f)
    }

    def withFilter (p: (L[T]) ⇒ Boolean): FilterMonadic[L[T], Traversable[L[T]]] = {
      lStream().withFilter(p)
    }

    def withFilter2(p: (L[T]) => Constraint[T]): FilterMonadic[L[T], Traversable[L[T]]] = {
      throw new Exception()
    }
  }

  implicit def lexpr2bool[T](l: LExpr[T]): Boolean = {
    val toAssert = lexprToExpr(l)
    // println("asserting within implicit call: " + toAssert)
    GlobalContext.assertConstraint(toAssert)
    GlobalContext.checkConsistency()
  }

  implicit def force[T](l : L[T]): T = {
    l.force()
  }

  def lexprToExpr(lexpr: LExpr[_]): Expr = lexpr match {
    case LEquals(l, r) => Equals(lexprToExpr(l), lexprToExpr(r))
    case LIntLiteral(i) => IntLiteral(i)
    case LBooleanLiteral(b) => BooleanLiteral(b)
    case LPlus(l, r) => Plus(lexprToExpr(l), lexprToExpr(r))
    case LMinus(l, r) => Minus(lexprToExpr(l), lexprToExpr(r))
    case LTimes(l, r) => Times(lexprToExpr(l), lexprToExpr(r))
    case LDivision(l, r) => Division(lexprToExpr(l), lexprToExpr(r))
    case LLessThan(l, r) => LessThan(lexprToExpr(l), lexprToExpr(r))
    case LGreaterThan(l, r) => GreaterThan(lexprToExpr(l), lexprToExpr(r))
    case LLessEquals(l, r) => LessEquals(lexprToExpr(l), lexprToExpr(r))
    case LGreaterEquals(l, r) => GreaterEquals(lexprToExpr(l), lexprToExpr(r))
    case LAnd(l, r) => And(lexprToExpr(l), lexprToExpr(r))
    case LOr(l, r) => Or(lexprToExpr(l), lexprToExpr(r))
    case LNot(l) => Not(lexprToExpr(l))
    case L(ids) => assert(ids.size == 1); Variable(ids.head)
  }

  sealed trait LExpr[T] {
    def ===(x: LExpr[T]): LExpr[Boolean] = LEquals(this, x)

    def +(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Int] = LPlus(this, x)
    def -(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Int] = LMinus(this, x)
    def *(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Int] = LTimes(this, x)
    def /(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Int] = LDivision(this, x)
    // def <(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Boolean] = LLessThan(this, x)
    def >(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Boolean] = LGreaterThan(this, x)
    def <=(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Boolean] = LLessEquals(this, x)
    def >=(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Int]): LExpr[Boolean] = LGreaterEquals(this, x)

    def &&(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Boolean]): LExpr[Boolean] = LAnd(this, x)
    def ||(x: LExpr[T])(implicit ev: LExpr[T] => LExpr[Boolean]): LExpr[Boolean] = LOr(this, x)
    def unary_!(implicit ev: LExpr[T] => LExpr[Boolean]): LExpr[Boolean] = LNot(this)
  }

  case class LEquals[T](lhs: LExpr[T], rhs: LExpr[T]) extends LExpr[Boolean]
  /* Literals */
  case class LIntLiteral(i: Int) extends LExpr[Int]
  case class LBooleanLiteral(b: Boolean) extends LExpr[Boolean]
  /* Arithmetic */
  case class LPlus(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Int]
  case class LMinus(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Int]
  case class LTimes(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Int]
  case class LDivision(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Int]
  case class LLessThan(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Boolean]
  case class LGreaterThan(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Boolean]
  case class LLessEquals(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Boolean]
  case class LGreaterEquals(lhs: LExpr[Int], rhs: LExpr[Int]) extends LExpr[Boolean]
  /* Propositional logic */
  case class LAnd(lhs: LExpr[Boolean], rhs: LExpr[Boolean]) extends LExpr[Boolean]
  case class LOr(lhs: LExpr[Boolean], rhs: LExpr[Boolean]) extends LExpr[Boolean]
  case class LNot(lexpr: LExpr[Boolean]) extends LExpr[Boolean]

  /* L for Lazy, L for Logic */
  object L {
    def unapply(l: L[_]): Option[Seq[Identifier]] = {
      if (l == null) None else Some(l.ids)
    }
  }

  class L[T](lStream: LStream[T], val ids: Seq[Identifier]) extends LExpr[T] {
    import ConstraintSolving.GlobalContext

    private def modelNegation(vs: Seq[Expr]): Expr = {
      Not(And(((ids map (i => Variable(i))) zip vs) map { case (i, v) => Equals(i, v) }))
    }

    def force(): T = {
      val model = GlobalContext.findValues(ids)
      val toRet = lStream.constraint.convertingFunction(model)
      GlobalContext.registerAsForced(ids, model)
      toRet
    }
  }
}
