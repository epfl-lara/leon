/**
  * Name:     GrammarRender.scala
  * Creation: 15.10.2015
  * Author:   Mika�l Mayer (mikael.mayer@epfl.ch)
  * Comments: Grammar rendering specifications.
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object GrammarRender {
  abstract class Symbol
  case class Terminal(i: Int) extends Symbol
  case class NonTerminal(i: Int) extends Symbol

  case class Rule(left: Symbol, right: List[Symbol])
  case class Grammar(start: Symbol, rules: List[Rule])

  /** Synthesis by example specs */
  @inline def psStandard(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) => "Grammar(NonTerminal(0), Nil())"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
      "Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil()))"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil())))"
  }

  @inline def psRemoveNames(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) => "(S0, ())"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
      "(S0, ((S0, (t1, ())), ()))"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "(S0, ((S0, (t1, ())), ((S0, (S0, (t1, ()))), ())))"
  }

  @inline def psArrowRules(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) => "(S0, ())"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
      "(S0, ((S0 -> (t1, ())), ()))"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "(S0, ((S0 -> (t1, ())), ((S0 -> (S0, (t1, ()))), ())))"
  }

  @inline def psListRules(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) => "(S0, [])"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
      "(S0, [S0 -> [t1]])"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "(S0, [S0 -> [t1], S0 -> [S0, t1])"
  }

  // The difficulty here is that two lists have to be rendered differently.
  @inline def psSpaceRules(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) => "(S0, [])"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
      "(S0, [S0 -> t1])"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "(S0, [S0 -> t1, S0 -> S0 t1)"
  }

  // Full HTML generation
  @inline def psHTMLRules(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) => "<b>Start:</b> S0<br><pre></pre>"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
      "<b>Start:</b> S0<br><pre>S0 -> t1</pte>"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "<b>Start:</b> S0<br><pre>S0 -> t1<br>S0 -> S0 t1</pte>"
  }
  //Render in plain text.
  @inline def psPlainTextRules(s: Grammar) = (res: String) => (s, res) passes {
    case Grammar(NonTerminal(0), Nil()) =>
    """Start:S0"""
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Nil())) =>
    """Start:S0
S0 -> t1"""
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
    """Start:S0
S0 -> t1
S0 -> S0 t1"""
  }
  
  /** Each function's body is the solution of the previous problem.
    * We want to check that the Leon can repair the programs and also find some ambiguities.*/
  def render0RemoveNames(s: Grammar): String = {
    def renderSymbol(s: Symbol) = s match {
      case NonTerminal(i) => "NonTerminal(" + i + ")"
      case Terminal(i) => "Terminal(" + i + ")"
    }
    def renderRule(r: Rule): String = {
      def renderListSymbol(s: List[Symbol]): String = s match {
        case Nil() => "Nil()"
        case Cons(a, q) => "Cons(" + rendersymbol(a) + ", " + renderListsymbol(q) + ")"
      }
      "Rule(" + renderSymbol(r.left) + ", " + renderListSymbol(r.right) + ")"
    }
    def renderListRules(s: List[Rules]): String = s match {
      case Nil() => "Nil()"
      case Cons(r, q) => "Cons(" + renderRule(r) + ", " + renderListRules(q) + ")"
    }
    "Grammar(" + renderSymbol(s.start) + ", " + renderListRules(s.rules) + ")"
  } ensuring psRemoveNames(s)
 
  def render1ArrowRules(s: Grammar): String = {
    def renderSymbol(s: Symbol) = s match {
      case NonTerminal(i) => "S" + i
      case Terminal(i) => "t" + i
    }
    def renderRule(r: Rule): String = {
      def renderListSymbol(s: List[Symbol]): String = s match {
        case Nil() => "()"
        case Cons(a, q) => "(" + rendersymbol(a) + ", " + renderListsymbol(q) + ")"
      }
      "(" + renderSymbol(r.left) + ", " + renderListSymbol(r.right) + ")"
    }
    def renderListRules(s: List[Rules]): String = s match {
      case Nil() => "()"
      case Cons(r, q) => "(" + renderRule(r) + ", " + renderListRules(q) + ")"
    }
    "(" + renderSymbol(s.start) + ", " + renderListRules(s.rules) + ")"
  } ensuring psArrowRules(s)

  def render2ListRules(s: Grammar): String = {
    def renderSymbol(s: Symbol) = s match {
      case NonTerminal(i) => "S" + i
      case Terminal(i) => "t" + i
    }
    def renderRule(r: Rule): String = {
      def renderListSymbol(s: List[Symbol]): String = s match {
        case Nil() => "()"
        case Cons(a, q) => "(" + rendersymbol(a) + ", " + renderListsymbol(q) + ")"
      }
      "(" + renderSymbol(r.left) + " -> " + renderListSymbol(r.right) + ")"
    }
    def renderListRules(s: List[Rules]): String = s match {
      case Nil() => "()"
      case Cons(r, q) => "(" + renderRule(r) + ", " + renderListRules(q) + ")"
    }
    "(" + renderSymbol(s.start) + ", " + renderListRules(s.rules) + ")"
  } ensuring psListRules(s)
  
  def render3SpaceRules(s: Grammar): String = {
    def renderSymbol(s: Symbol) = s match {
      case NonTerminal(i) => "S" + i
      case Terminal(i) => "t" + i
    }
    def renderRule(r: Rule): String = {
      def renderListSymbol(s: List[Symbol]): String = s match {
        case Nil() => ""
        case Cons(a, Nil()) => rendersymbol(a)
        case Cons(a, q) => rendersymbol(a) + ", " + renderListsymbol(q)
      }
      renderSymbol(r.left) + " -> [" + renderListSymbol(r.right) + "]"
    }
    def renderListRules(s: List[Rules]): String = s match {
      case Nil() => ""
      case Cons(r, Nil()) => renderRule(r)
      case Cons(r, q) => renderRule(r) + ", " + renderListRules(q)
    }
    "(" + renderSymbol(s.start) + ", [" + renderListRules(s.rules) + "])"
  } ensuring psSpaceRules(s)

  def render4HTMLRules(s: Grammar): String = {
    def renderSymbol(s: Symbol) = s match {
      case NonTerminal(i) => "S" + i
      case Terminal(i) => "t" + i
    }
    def renderRule(r: Rule): String = {
      def renderListSymbol(s: List[Symbol]): String = s match {
        case Nil() => ""
        case Cons(a, Nil()) => rendersymbol(a)
        case Cons(a, q) => rendersymbol(a) + " " + renderListsymbol(q)
      }
      renderSymbol(r.left) + " -> " + renderListSymbol(r.right) + ""
    }
    def renderListRules(s: List[Rules]): String = s match {
      case Nil() => ""
      case Cons(r, Nil()) => renderRule(r)
      case Cons(r, q) => renderRule(r) + ", " + renderListRules(q)
    }
    "(" + renderSymbol(s.start) + ", [" + renderListRules(s.rules) + "])"
  } ensuring psHTMLRules(s)
  
  /* The initial body of this function is the solution of render3 */
  def render5PlainTextRules(s: Grammar): String = {
    def renderSymbol(s: Symbol) = s match {
      case NonTerminal(i) => "S" + i
      case Terminal(i) => "t" + i
    }
    def renderRule(r: Rule): String = {
      def renderListSymbol(s: List[Symbol]): String = s match {
        case Nil() => ""
        case Cons(a, Nil()) => rendersymbol(a)
        case Cons(a, q) => rendersymbol(a) + " " + renderListsymbol(q)
      }
      renderSymbol(r.left) + " -> " + renderListSymbol(r.right) + ""
    }
    def renderListRules(s: List[Rules]): String = s match {
      case Nil() => ""
      case Cons(r, Nil()) => renderRule(r)
      case Cons(r, q) => renderRule(r) + ", " + renderListRules(q)
    }
    "(" + renderSymbol(s.start) + ", [" + renderListRules(s.rules) + "])"
  } ensuring psPlainTextRules(s)

  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def synthesizeStandard(s: Grammar): String = {
    ???[String]
  } ensuring psStandard(s)
  
  def synthesizeRemoveNames(s: Grammar): String = {
    ???[String]
  } ensuring psRemoveNames(s)

  def synthesizeArrowRules(s: Grammar): String = {
    ???[String]
  } ensuring psArrowRules(s)

  def synthesizeListRules(s: Grammar): String = {
    ???[String]
  } ensuring psListRules(s)

  def synthesizeSpaceRules(s: Grammar): String = {
    ???[String]
  } ensuring psSpaceRules(s)

  def synthesizeHTMLRules(s: Grammar): String = {
    ???[String]
  } ensuring psHTMLRules(s)

  def synthesizePlainTextRules(s: Grammar): String = {
    ???[String]
  } ensuring psPlainTextRules(s)
  
  def allGrammarsAreIdentical(g: Grammar, g2: Grammar) = (g == g2 || g.rules == g2.rules) holds

}