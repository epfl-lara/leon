package leon.solvers.isabelle

import scala.concurrent._
import scala.math.BigInt

import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps
import leon.purescala.Types._
import leon.utils._

import edu.tum.cs.isabelle._

final class Translator(context: LeonContext, program: Program, types: Types, system: System)(implicit ec: ExecutionContext) {

  private implicit val debugSection = DebugSectionIsabelle

  private def mkApp(f: Term, args: Term*): Term =
    args.foldLeft(f) { (acc, arg) => App(acc, arg) }

  private def lookupConstructor(typ: CaseClassType): Future[Constructor] =
    types.data.map(_.get(Types.findRoot(typ).classDef).flatMap(_.constructors.get(typ.classDef)) match {
      case Some(constr) => constr
      case None => context.reporter.internalError(s"$typ not found in program")
    })

  private def mkFresh(typ: Option[TypeTree]) =
    system.invoke(Fresh)("fresh''").assertSuccess(context).flatMap { name =>
      types.optTyp(typ).map(Free(name, _))
    }

  def mkFreshError(typ: Option[TypeTree]): Future[Term] =
    system.invoke(SerialNat)(()).assertSuccess(context).flatMap { nat =>
      types.optTyp(typ).map { typ =>
        App(Const("Leon_Library.error", Type("fun", List(Typ.dummyT, typ))), nat)
      }
    }

  private def arity(typ: TypeTree): Int = typ match {
    case t: TupleType => t.dimension
    case _ => context.reporter.internalError(s"Expected tuple type, got $typ")
  }

  def term(expr: Expr, bounds: List[Identifier], consts: (FunDef, Typ) => Term): Future[Term] = {
    def mkAbs(params: List[Identifier], body: Expr, bounds: List[Identifier], wrap: Term => Term = identity): Future[Term] = params match {
      case Nil => term(body, bounds, consts)
      case p :: ps =>
        for {
          rec <- mkAbs(ps, body, p :: bounds, wrap)
          typ <- types.typ(p.getType)
        }
        yield
          wrap(Abs(p.mangledName /* name hint, no logical content */, typ, rec))
    }

    def nary(const: Term, xs: Expr*) =
      Future.traverse(xs.toList)(term(_, bounds, consts)).map(ts => mkApp(const, ts: _*))

    def flexary1(const: Term, xs: Seq[Expr]) =
      Future.traverse(xs.toList)(term(_, bounds, consts)).map(_.reduceRight { (t, acc) => mkApp(const, t, acc) })

    def flexary(const: Term, init: Term, xs: Seq[Expr]) =
      Future.traverse(xs.toList)(term(_, bounds, consts)).map(_.foldRight(init) { (t, acc) => mkApp(const, t, acc) })

    def inSet(set: Term, elem: Expr) =
      term(elem, bounds, consts).map(mkApp(Const("Set.member", Typ.dummyT), _, set))

    def lets(bindings: List[(Identifier, Term)], body: Expr) = {
      val referenced = ExprOps.variablesOf(body)
      val filtered = bindings.filter { case (id, _) => referenced contains id }

      val (names, rhss) = filtered.unzip
      rhss.foldLeft(mkAbs(names, body, bounds)) { (term, rhs) =>
        term.map(mkApp(Const("HOL.Let", Typ.dummyT), rhs, _))
      }
    }

    def let(name: Identifier, rhs: Term, body: Expr) =
      lets(List(name -> rhs), body)

    def precondition(pred: Expr, body: Expr) =
      for {
        p <- term(pred, bounds, consts)
        b <- term(body, bounds, consts)
        e <- mkFreshError(Some(body.getType))
      }
      yield
        mkApp(Const("HOL.If", Typ.dummyT), p, b, e)

    def postcondition(pred: Expr, body: Expr) =
      for {
        p <- term(pred, bounds, consts)
        b <- term(body, bounds, consts)
        e <- mkFreshError(Some(body.getType))
      }
      yield
        mkApp(Const("HOL.If", Typ.dummyT), App(p, b), b, e)

    def pattern(pat: Pattern): Future[Option[(Term, List[(Identifier, Term)])]] = {
      val res = pat match {
        case CaseClassPattern(_, typ, pats) =>
          Future.traverse(pats.toList)(pattern).flatMap { _.sequence match {
            case Some(args) =>
              val (pats, bindings) = args.unzip

              lookupConstructor(typ).map(_.term).map { head =>
                Some((mkApp(head, pats: _*), bindings.flatten))
              }
            case None =>
              Future.successful(None)
          }}

        case InstanceOfPattern(_, typ: CaseClassType) =>
          lookupConstructor(typ).flatMap { case Constructor(term, _, sels) =>
            val length = sels.size
            Future.traverse(1 to length) { _ => mkFresh(None) }.map { vars =>
              Some((mkApp(term, vars: _*), Nil))
            }
          }

        case TuplePattern(_, pats) =>
          Future.traverse(pats.toList)(pattern).map { _.sequence match {
            case Some(args) =>
              val (pats, bindings) = args.unzip
              val pat = pats.reduceRight { (p, acc) => mkApp(Const("Product_Type.Pair", Typ.dummyT), p, acc) }
              Some(pat, bindings.flatten)
            case None =>
              None
          }}

        case WildcardPattern(None) =>
          mkFresh(pat.binder.map(_.getType)).map { term => Some((term, Nil)) }

        case WildcardPattern(Some(id)) =>
          types.typ(id.getType).map { typ => Some((Free(id.mangledName, typ), Nil)) }

        case _ =>
          Future.successful(None)
      }

      val bind = pat match {
        case WildcardPattern(_) => false
        case _ => true
      }

      pat.binder match {
        case Some(id) if bind => res.map(_.map { case (term, bindings) =>
          (term, (id -> term) :: bindings)
        })
        case _ => res
      }
    }

    def clause(clause: MatchCase) = clause.optGuard match {
      case Some(_) =>
        Future.successful(None)
      case None =>
        pattern(clause.pattern).flatMap {
          case Some((pat, bindings)) =>
            lets(bindings, clause.rhs).map { term => Some(pat -> term) }
          case None =>
            Future.successful(None)
        }
    }

    expr match {
      case Variable(id) =>
        types.typ(id.getType) map { typ =>
          bounds.indexOf(id) match {
            case -1 => Free(id.mangledName, typ)
            case n => Bound(n)
          }
        }

      case Let(x, t, y) =>
        term(t, bounds, consts).flatMap { let(x, _, y) }

      case Lambda(args, expr) =>
        mkAbs(args.map(_.id).toList, expr, bounds)

      case Forall(args, expr) =>
        mkAbs(args.map(_.id).toList, expr, bounds, wrap = mkApp(Const("HOL.All", Typ.dummyT), _))

      case CaseClass(typ, exprs) =>
        lookupConstructor(typ).map(_.term).flatMap { nary(_, exprs: _*) }

      case CaseClassSelector(typ, expr, sel) =>
        lookupConstructor(typ).map(_.sels.collectFirst {
          case (field, term) if field.id == sel => term
        }).flatMap {
          case Some(term) => nary(term, expr)
          case None => context.reporter.internalError(s"$typ or $sel not found in program")
        }

      case IsInstanceOf(expr, typ: CaseClassType) =>
        lookupConstructor(typ).map(_.disc).flatMap { nary(_, expr) }

      case AsInstanceOf(expr, _) =>
        term(expr, bounds, consts)

      case Tuple(exprs) =>
        flexary1(Const("Product_Type.Pair", Typ.dummyT), exprs)

      case TupleSelect(expr, i) =>
        def sel(i: Int, len: Int, term: Term): Term = (i, len) match {
          case (1, _) => App(Const("Product_Type.prod.fst", Typ.dummyT), term)
          case (2, 2) => App(Const("Product_Type.prod.snd", Typ.dummyT), term)
          case _ => App(Const("Product_Type.prod.snd", Typ.dummyT), sel(i - 1, len - 1, term))
        }

        term(expr, bounds, consts).map(sel(i, arity(expr.getType), _))

      case MatchExpr(scrutinee, clauses) =>
        term(scrutinee, bounds, consts).flatMap { scrutinee =>
          Future.traverse(clauses.toList)(clause).flatMap { _.sequence match {
            case Some(clauses) =>
              val catchall =
                for {
                  pat <- mkFresh(None)
                  rhs <- mkFreshError(Some(expr.getType))
                }
                yield (pat, rhs)

              types.typ(expr.getType).flatMap { typ =>
                catchall.flatMap { catchall =>
                  Future.traverse(bounds) { id =>
                    types.typ(id.getType).map(id.mangledName -> _)
                  }.flatMap { bounds =>
                    system.invoke(Cases)(((scrutinee, bounds), (typ, clauses :+ catchall))).assertSuccess(context)
                  }
                }
              }
            case None =>
              context.reporter.warning("Match uses unsupported features; translating to if-then-else")
              term(ExprOps.matchToIfThenElse(expr), bounds, consts)
          }}
        }

      case FunctionInvocation(fun, args) =>
        types.functionTyp(args.map(_.getType), expr.getType).flatMap { typ =>
          nary(consts(fun.fd, typ), args: _*)
        }

      case Application(fun, args) =>
        term(fun, bounds, consts).flatMap(nary(_, args: _*))

      case Error(tpe, _) =>
        mkFreshError(Some(tpe))

      case UnitLiteral() =>         Future.successful { Const("Product_Type.Unity", Typ.dummyT) }
      case BooleanLiteral(true) =>  Future.successful { Const("HOL.True", Typ.dummyT) }
      case BooleanLiteral(false) => Future.successful { Const("HOL.False", Typ.dummyT) }

      case InfiniteIntegerLiteral(n) =>
        system.invoke(NumeralLiteral)((n, Type("Int.int", Nil))).assertSuccess(context)

      case CharLiteral(c) =>
        types.char.flatMap(typ => system.invoke(NumeralLiteral)((c.toLong, typ))).assertSuccess(context)

      case IntLiteral(n) =>
        types.typ(expr.getType).flatMap(typ => system.invoke(NumeralLiteral)((n, typ))).assertSuccess(context)

      case Assert(pred, _, body) => precondition(pred, body)
      case Require(pred, body) =>   precondition(pred, body)
      case Ensuring(body, pred) =>  postcondition(pred, body)

      case IfExpr(x, y, z) => nary(Const("HOL.If", Typ.dummyT), x, y, z)
      case Not(x) =>          nary(Const("HOL.Not", Typ.dummyT), x)
      case Implies(x, y) =>   nary(Const("HOL.implies", Typ.dummyT), x, y)
      case And(xs) =>         flexary1(Const("HOL.conj", Typ.dummyT), xs)
      case Or(xs) =>          flexary1(Const("HOL.disj", Typ.dummyT), xs)

      // Isabelle doesn't have > or >=, need to swap operands in these cases
      case Equals(x, y) =>        nary(Const("HOL.eq", Typ.dummyT), x, y)
      case LessThan(x, y) =>      nary(Const("Orderings.ord_class.less", Typ.dummyT), x, y)
      case LessEquals(x, y) =>    nary(Const("Orderings.ord_class.less_eq", Typ.dummyT), x, y)
      case GreaterThan(x, y) =>   nary(Const("Orderings.ord_class.less", Typ.dummyT), y, x)
      case GreaterEquals(x, y) => nary(Const("Orderings.ord_class.less_eq", Typ.dummyT), y, x)

      case Plus(x, y) =>  nary(Const("Groups.plus_class.plus", Typ.dummyT), x, y)
      case Minus(x, y) => nary(Const("Groups.minus_class.minus", Typ.dummyT), x, y)
      case UMinus(x) =>   nary(Const("Groups.uminus_class.uminus", Typ.dummyT), x)
      case Times(x, y) => nary(Const("Groups.times_class.times", Typ.dummyT), x, y)

      case RealPlus(x, y) =>  nary(Const("Groups.plus_class.plus", Typ.dummyT), x, y)
      case RealMinus(x, y) => nary(Const("Groups.minus_class.minus", Typ.dummyT), x, y)
      case RealUMinus(x) =>   nary(Const("Groups.uminus_class.uminus", Typ.dummyT), x)
      case RealTimes(x, y) => nary(Const("Groups.times_class.times", Typ.dummyT), x, y)

      case FiniteSet(elems, _) =>   flexary(Const("Set.insert", Typ.dummyT), Const("Set.empty", Typ.dummyT), elems.toList)
      case SetUnion(x, y) =>        nary(Const("Lattices.sup_class.sup", Typ.dummyT), x, y)
      case SetIntersection(x, y) => nary(Const("Lattices.inf_class.inf", Typ.dummyT), x, y)
      case SetDifference(x, y) =>   nary(Const("Groups.minus_class.minus", Typ.dummyT), x, y)
      case SubsetOf(x, y) =>        nary(Const("Orderings.ord_class.less_eq", Typ.dummyT), x, y)
      case ElementOfSet(elem, set) => term(set, bounds, consts).flatMap(inSet(_, elem))

      case FiniteMap(elems, from, to) =>
        val es = Future.traverse(elems.toList) { case (k, v) => term(k, bounds, consts) zip term(v, bounds, consts) }
        for {
          f <- types.typ(from)
          t <- types.typ(to)
          es <- es
          res <- system.invoke(MapLiteral)((es, (f, t))).assertSuccess(context)
        }
        yield res

      case MapApply(map, key) =>
        term(map, bounds, consts).flatMap(nary(_, key)).map(App(Const("Option.option.the", Typ.dummyT), _))
      case MapIsDefinedAt(map, key) =>
        term(map, bounds, consts).flatMap { map =>
          inSet(App(Const("Map.dom", Typ.dummyT), map), key)
        }
      case MapUnion(x, y) => nary(Const("Map.map_add", Typ.dummyT), x, y)

      case Choose(pred) =>
        nary(Const("Hilbert_Choice.Eps", Typ.dummyT), pred)

      case _ =>
        context.reporter.warning(s"Unknown expression $expr, translating to unspecified term")
        mkFreshError(Some(expr.getType))
    }
  }

}
