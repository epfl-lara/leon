package leon
package purescala

import Trees._

object Extractors {
  object UnaryOperator {
    def unapply(expr: Expr) : Option[(Expr,(Expr)=>Expr)] = expr match {
      case Not(t) => Some((t,Not(_)))
      case UMinus(t) => Some((t,UMinus))
      case SetCardinality(t) => Some((t,SetCardinality))
      case MultisetCardinality(t) => Some((t,MultisetCardinality))
      case MultisetToSet(t) => Some((t,MultisetToSet))
      case Car(t) => Some((t,Car))
      case Cdr(t) => Some((t,Cdr))
      case SetMin(s) => Some((s,SetMin))
      case SetMax(s) => Some((s,SetMax))
      case CaseClassSelector(cd, e, sel) => Some((e, CaseClassSelector(cd, _, sel)))
      case CaseClassInstanceOf(cd, e) => Some((e, CaseClassInstanceOf(cd, _)))
      case Assignment(id, e) => Some((e, Assignment(id, _)))
      case TupleSelect(t, i) => Some((t, TupleSelect(_, i)))
      case ArrayLength(a) => Some((a, ArrayLength))
      case ArrayClone(a) => Some((a, ArrayClone))
      case ArrayMake(t) => Some((t, ArrayMake))
      case Waypoint(i, t) => Some((t, (expr: Expr) => Waypoint(i, expr)))
      case e@Epsilon(t) => Some((t, (expr: Expr) => Epsilon(expr).setType(e.getType).setPosInfo(e)))
      case _ => None
    }
  }

  object BinaryOperator {
    def unapply(expr: Expr) : Option[(Expr,Expr,(Expr,Expr)=>Expr)] = expr match {
      case Equals(t1,t2) => Some((t1,t2,Equals.apply))
      case Iff(t1,t2) => Some((t1,t2,Iff(_,_)))
      case Implies(t1,t2) => Some((t1,t2,Implies.apply))
      case Plus(t1,t2) => Some((t1,t2,Plus))
      case Minus(t1,t2) => Some((t1,t2,Minus))
      case Times(t1,t2) => Some((t1,t2,Times))
      case Division(t1,t2) => Some((t1,t2,Division))
      case Modulo(t1,t2) => Some((t1,t2,Modulo))
      case LessThan(t1,t2) => Some((t1,t2,LessThan))
      case GreaterThan(t1,t2) => Some((t1,t2,GreaterThan))
      case LessEquals(t1,t2) => Some((t1,t2,LessEquals))
      case GreaterEquals(t1,t2) => Some((t1,t2,GreaterEquals))
      case ElementOfSet(t1,t2) => Some((t1,t2,ElementOfSet))
      case SubsetOf(t1,t2) => Some((t1,t2,SubsetOf))
      case SetIntersection(t1,t2) => Some((t1,t2,SetIntersection))
      case SetUnion(t1,t2) => Some((t1,t2,SetUnion))
      case SetDifference(t1,t2) => Some((t1,t2,SetDifference))
      case Multiplicity(t1,t2) => Some((t1,t2,Multiplicity))
      case SubmultisetOf(t1,t2) => Some((t1,t2,SubmultisetOf))
      case MultisetIntersection(t1,t2) => Some((t1,t2,MultisetIntersection))
      case MultisetUnion(t1,t2) => Some((t1,t2,MultisetUnion))
      case MultisetPlus(t1,t2) => Some((t1,t2,MultisetPlus))
      case MultisetDifference(t1,t2) => Some((t1,t2,MultisetDifference))
      case SingletonMap(t1,t2) => Some((t1,t2,SingletonMap))
      case mg@MapGet(t1,t2) => Some((t1,t2, (t1, t2) => MapGet(t1, t2).setPosInfo(mg)))
      case MapUnion(t1,t2) => Some((t1,t2,MapUnion))
      case MapDifference(t1,t2) => Some((t1,t2,MapDifference))
      case MapIsDefinedAt(t1,t2) => Some((t1,t2, MapIsDefinedAt))
      case ArrayFill(t1, t2) => Some((t1, t2, ArrayFill))
      case ArraySelect(t1, t2) => Some((t1, t2, ArraySelect))
      case Concat(t1,t2) => Some((t1,t2,Concat))
      case ListAt(t1,t2) => Some((t1,t2,ListAt))
      case wh@While(t1, t2) => Some((t1,t2, (t1, t2) => While(t1, t2).setInvariant(wh.invariant).setPosInfo(wh)))
      case _ => None
    }
  }

  object NAryOperator {
    def unapply(expr: Expr) : Option[(Seq[Expr],(Seq[Expr])=>Expr)] = expr match {
      case fi @ FunctionInvocation(fd, args) => Some((args, (as => FunctionInvocation(fd, as).setPosInfo(fi))))
      case AnonymousFunctionInvocation(id, args) => Some((args, (as => AnonymousFunctionInvocation(id, as))))
      case CaseClass(cd, args) => Some((args, CaseClass(cd, _)))
      case And(args) => Some((args, And.apply))
      case Or(args) => Some((args, Or.apply))
      case FiniteSet(args) => Some((args, FiniteSet))
      case FiniteMap(args) => Some((args, (as : Seq[Expr]) => FiniteMap(as.asInstanceOf[Seq[SingletonMap]])))
      case FiniteMultiset(args) => Some((args, FiniteMultiset))
      case ArrayUpdate(t1, t2, t3) => Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdate(as(0), as(1), as(2))))
      case ArrayUpdated(t1, t2, t3) => Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdated(as(0), as(1), as(2))))
      case FiniteArray(args) => Some((args, FiniteArray))
      case Distinct(args) => Some((args, Distinct))
      case Block(args, rest) => Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
      case Tuple(args) => Some((args, Tuple))
      case _ => None
    }
  }
}
