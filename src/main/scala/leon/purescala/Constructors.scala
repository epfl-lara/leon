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

  // If isTuple, the whole expression is returned. This is to avoid a situation
  // like tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> x, which is not expected.
  // Instead, tupleSelect(tupleWrap(Seq(Tuple(x,y))),1) -> Tuple(x,y).
  def tupleSelect(t: Expr, index: Int, isTuple: Boolean): Expr = t match {
    case Tuple(es) if isTuple => es(index-1)
    case _ if t.getType.isInstanceOf[TupleType] && isTuple =>
      TupleSelect(t, index)
    case other if !isTuple => other
    case _ =>
      sys.error(s"Calling tupleSelect on non-tuple $t")
  }

  def tupleSelect(t: Expr, index: Int, originalSize: Int): Expr = tupleSelect(t, index, originalSize > 1)

  def letTuple(binders: Seq[Identifier], value: Expr, body: Expr) = binders match {
    case Nil =>
      body
    case x :: Nil =>
      Let(x, value, body)
    case xs =>
      require(
        value.getType.isInstanceOf[TupleType],
        s"The definition value in LetTuple must be of some tuple type; yet we got [${value.getType}]. In expr: \n$this"
      )

      Extractors.LetPattern(TuplePattern(None,binders map { b => WildcardPattern(Some(b)) }), value, body)
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

  def finiteSet(els: Set[Expr], tpe: TypeTree) = {
    if (els.isEmpty) EmptySet(tpe)
    else NonemptySet(els)
  }

  def finiteMultiset(els: Seq[Expr], tpe: TypeTree) = {
    if (els.isEmpty) EmptyMultiset(tpe)
    else NonemptyMultiset(els)
  }

  def finiteMap(els: Seq[(Expr, Expr)], keyType: TypeTree, valueType: TypeTree) = {
    if (els.isEmpty) EmptyMap(keyType, valueType)
    else NonemptyMap(els.distinct)
  }

  def finiteArray(els: Seq[Expr]): Expr = {
    require(!els.isEmpty)
    finiteArray(els, None, Untyped) // Untyped is not correct, but will not be used anyway 
  }

  def finiteArray(els: Seq[Expr], defaultLength: Option[(Expr, Expr)], tpe: TypeTree): Expr = {
    finiteArray(els.zipWithIndex.map{ _.swap }.toMap, defaultLength, tpe)
  }

  def finiteArray(els: Map[Int, Expr], defaultLength: Option[(Expr, Expr)], tpe: TypeTree): Expr = {
    if (els.isEmpty && defaultLength.isEmpty) EmptyArray(tpe)
    else NonemptyArray(els, defaultLength)
  }
  
  def finiteLambda(default: Expr, els: Seq[(Expr, Expr)], inputTypes: Seq[TypeTree]): Lambda = {
    val args = inputTypes map { tpe => ValDef(FreshIdentifier("x", tpe, true)) }
    if (els.isEmpty) {
      Lambda(args, default)
    } else {
      val theMap = NonemptyMap(els)
      val theMapVar = FreshIdentifier("pairs", theMap.getType, true)
      val argsAsExpr = tupleWrap(args map { _.toVariable })
      val body = Let(theMapVar, theMap,  IfExpr(
        MapIsDefinedAt(Variable(theMapVar), argsAsExpr), 
        MapGet(Variable(theMapVar), argsAsExpr), 
        default
      ))
      Lambda(args, body)
    }
  }
}
