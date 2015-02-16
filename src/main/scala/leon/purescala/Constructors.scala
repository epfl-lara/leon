/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

object Constructors {
  import Trees._
  import Definitions._
  import TypeTreeOps._
  import Common._
  import TypeTrees._

  def tupleSelect(t: Expr, index: Int) = t match {
    case Tuple(es) =>
      es(index-1)
    case _ =>
      TupleSelect(t, index)
  }

  def letTuple(binders: Seq[Identifier], value: Expr, body: Expr) = binders match {
    case Nil =>
      body
    case x :: Nil =>
      if (isSubtypeOf(value.getType, x.getType) || !value.getType.isInstanceOf[TupleType]) {
        // This is for cases where we build it like: letTuple(List(x), tupleWrap(List(z)))
        Let(x, value, body)
      } else {
        Let(x, tupleSelect(value, 1), body)
      }
    case xs =>
      require(
        value.getType.isInstanceOf[TupleType],
        s"The definition value in LetTuple must be of some tuple type; yet we got [${value.getType}]. In expr: \n$this"
      )

      Extractors.LetPattern(TuplePattern(None,binders map { b => WildcardPattern(Some(b)) }), value, body)
  }

  def tupleChoose(ch: Choose): Expr = {
    if (ch.vars.size > 1) {
      ch
    } else {
      Tuple(Seq(ch))
    }
  }

  def tupleWrap(es: Seq[Expr]): Expr = es match {
    case Seq() => UnitLiteral()
    case Seq(elem) => elem 
    case more => Tuple(more)
  }
  
  def tuplePatternWrap(ps: Seq[Pattern]) = ps match {
    case Seq() => LiteralPattern(None, UnitLiteral())
    case Seq(elem) => elem
    case more => TuplePattern(None, more)
  }
  
  def tupleTypeWrap(tps : Seq[TypeTree]) = tps match {
    case Seq() => UnitType
    case Seq(elem) => elem
    case more => TupleType(more)
  }

  /** Will instantiate the type parameters of the function according to argument types */
  def functionInvocation(fd : FunDef, args : Seq[Expr]) = {
    
    require(fd.params.length == args.length)
    
    val formalType = tupleTypeWrap(fd.params map { _.getType })
    val actualType = tupleTypeWrap(args map { _.getType })
    
    canBeSubtypeOf(actualType, typeParamsOf(formalType).toSeq, formalType) match {
      case Some(tmap) =>
        FunctionInvocation(fd.typed(fd.tparams map { tpd => tmap.getOrElse(tpd.tp, tpd.tp) }), args)
      case None => sys.error(s"$actualType cannot be a subtype of $formalType!")
    }

   
  }
  
  private def filterCases(scrutType : TypeTree, resType: Option[TypeTree], cases: Seq[MatchCase]): Seq[MatchCase] = {
    val casesFiltered = scrutType match {
      case c: CaseClassType =>
        cases.filter(_.pattern match {
          case CaseClassPattern(_, cct, _) if cct.classDef != c.classDef => false
          case _ => true
        })

      case _: TupleType | Int32Type | BooleanType | UnitType | _: AbstractClassType =>
        cases

      case t =>
        scala.sys.error("Constructing match expression on non-supported type: "+t)
    }

    resType match {
      case Some(tpe) =>
        casesFiltered.filter(c => isSubtypeOf(c.rhs.getType, tpe) || isSubtypeOf(tpe, c.rhs.getType))
      case None =>
        casesFiltered
    }
  }

  def gives(scrutinee : Expr, cases : Seq[MatchCase]) : Gives =
    Gives(scrutinee, filterCases(scrutinee.getType, None, cases))
  
  def passes(in : Expr, out : Expr, cases : Seq[MatchCase]): Expr = {
    val resultingCases = filterCases(in.getType, Some(out.getType), cases)
    if (resultingCases.nonEmpty) {
      Passes(in, out, resultingCases)
    } else {
      BooleanLiteral(true)
    }
  }

  def matchExpr(scrutinee : Expr, cases : Seq[MatchCase]) : Expr ={
    val filtered = filterCases(scrutinee.getType, None, cases)
    if (filtered.nonEmpty)
      MatchExpr(scrutinee, filtered)
    else 
      Error(
        cases match {
          case Seq(hd, _*) => hd.rhs.getType
          case Seq() => Untyped
        },
        "No case matches the scrutinee"
      )
  } 
    
   

  def and(exprs: Expr*): Expr = {
    val flat = exprs.flatMap(_ match {
      case And(es) => es
      case o => Seq(o)
    })

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(true)) yield {
      if(e == BooleanLiteral(false)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(true)
      case Seq(x) => x
      case _      => And(simpler)
    }
  }

  def andJoin(es: Seq[Expr]) = and(es :_*)

  def or(exprs: Expr*): Expr = {
    val flat = exprs.flatMap(_ match {
      case Or(es) => es
      case o => Seq(o)
    })

    var stop = false
    val simpler = for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
      if(e == BooleanLiteral(true)) stop = true
      e
    }

    simpler match {
      case Seq()  => BooleanLiteral(false)
      case Seq(x) => x
      case _      => Or(simpler)
    }
  }

  def orJoin(es: Seq[Expr]) = or(es :_*)

  def not(e: Expr): Expr = e match {
    case Not(e)            => e
    case BooleanLiteral(v) => BooleanLiteral(!v)
    case _                 => Not(e)
  }

  def implies(lhs: Expr, rhs: Expr): Expr = (lhs, rhs) match {
    case (BooleanLiteral(false), _) => BooleanLiteral(true)
    case (_, BooleanLiteral(true))  => BooleanLiteral(true)
    case (BooleanLiteral(true), r)  => r
    case (l, BooleanLiteral(false)) => Not(l)
    case (l1, Implies(l2, r2))      => implies(and(l1, l2), r2)
    case _                          => Implies(lhs, rhs)
  }

  def finiteLambda(dflt: Expr, els: Seq[(Expr, Expr)], tpe: FunctionType): Lambda = {
    val args = tpe.from.zipWithIndex.map { case (tpe, idx) =>
      ValDef(FreshIdentifier(s"x${idx + 1}").setType(tpe), tpe)
    }

    assume(els.isEmpty || !tpe.from.isEmpty, "Can't provide finite mapping for lambda without parameters")

    lazy val (tupleArgs, tupleKey) = if (tpe.from.size > 1) {
      val tpArgs = Tuple(args.map(_.toVariable))
      val key = (x: Expr) => x
      (tpArgs, key)
    } else { // note that value is lazy, so if tpe.from.size == 0, foldRight will never access (tupleArgs, tupleKey)
      val tpArgs = args.head.toVariable
      val key = (x: Expr) => {
        if (isSubtypeOf(x.getType, tpe.from.head)) x
        else if (isSubtypeOf(x.getType, TupleType(tpe.from))) x.asInstanceOf[Tuple].exprs.head
        else throw new RuntimeException("Can't determine key tuple state : " + x + " of " + tpe)
      }
      (tpArgs, key)
    }

    val body = els.toSeq.foldRight(dflt) { case ((k, v), elze) =>
      IfExpr(Equals(tupleArgs, tupleKey(k)), v, elze)
    }

    Lambda(args, body)
  }
  
}
