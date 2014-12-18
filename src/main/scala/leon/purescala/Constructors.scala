/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

object Constructors {
  import Trees._
  import TypeTreeOps._
  import Common._
  import TypeTrees._
  import Definitions.FunDef

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
      Let(x, tupleSelect(value, 1), body)
    case xs =>
      LetTuple(xs, value, body)
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

  def functionInvocation(fd : FunDef, args : Seq[Expr]) = {
    
    def unifyMany(ts1 : Seq[TypeTree], ts2 : Seq[TypeTree]) = {
      ts1.zip(ts2).map{ case (t1, t2) => unify(t1,t2) }.foldLeft(Map[Identifier, TypeTree]())(_ ++ _)
    }
    
    def unify(t1 : TypeTree, t2 : TypeTree) : Map[Identifier, TypeTree] = (t1,t2) match {
      case (TypeParameter(id), _) => Map(id -> t2)
      case (_, TypeParameter(id)) => Map(id -> t1)
      case (BooleanType, BooleanType) |
           (Int32Type, Int32Type) |
           (UnitType, UnitType) |
           (CharType, CharType) => Map()
      case (TupleType(bases1), TupleType(bases2)) => 
        unifyMany(bases1, bases2)
      case (SetType(base1), SetType(base2)) => 
        unify(base1,base2)
      case (ArrayType(base1), ArrayType(base2)) => 
        unify(base1,base2)
      case (MultisetType(base1), MultisetType(base2)) => 
        unify(base1,base2)
      case (MapType(from1, to1), MapType(from2, to2)) => 
        unify(from1, from2) ++ unify(to1,to2)
      case (FunctionType(from1, to1), FunctionType(from2, to2)) => 
        unifyMany(to1 :: from1, to2 :: from2)
      case (TupleType(bases1), TupleType(bases2)) => 
        unifyMany(bases1, bases2)
      case (c1 : ClassType, c2 : ClassType) if isSubtypeOf(c1, c2) || isSubtypeOf(c2,c1) =>
        unifyMany(c1.tps, c2.tps)
      case _ => throw new java.lang.IllegalArgumentException()
    }
    
    require(fd.params.length == args.length)
    val typeInstantiations = unifyMany(fd.params map { _.getType}, args map { _.getType })
    val tps = fd.tparams map { tpar => typeInstantiations(tpar.id) }
    FunctionInvocation(fd.typed(tps), args)
    
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
  
}
