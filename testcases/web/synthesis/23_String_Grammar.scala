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
      "<b>Start:</b> S0<br><pre>S0 -> t1</pre>"
    case Grammar(NonTerminal(0), Cons(Rule(NonTerminal(0), Cons(Terminal(1), Nil())), Cons(Rule(NonTerminal(0), Cons(NonTerminal(0), Cons(Terminal(1), Nil()))), Nil()))) =>
      "<b>Start:</b> S0<br><pre>S0 -> t1<br>S0 -> S0 t1</pre>"
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
  
  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  /*def synthesizeStandard(s: Grammar): String = {
    ???[String]
  } ensuring psStandard(s)*/
  
  /*def synthesizeRemoveNames(s: Grammar): String = {
    ???[String]
  } ensuring psRemoveNames(s)*/

  /*def synthesizeArrowRules(s: Grammar): String = {
    ???[String]
  } ensuring psArrowRules(s)*/

  /*def synthesizeListRules(s: Grammar): String = {
    ???[String]
  } ensuring psListRules(s)*/

  /*def synthesizeSpaceRules(s: Grammar): String = {
    ???[String]
  } ensuring psSpaceRules(s)*/

  /*def synthesizeHTMLRules(s: Grammar): String = {
    ???[String]
  } ensuring psHTMLRules(s)*/

  /*def synthesizePlainTextRulesToString(s: Grammar): String = {
    ???[String]
  } ensuring psPlainTextRules(s)*/
  
  def isTerminal(s: Symbol) = s match {
    case Terminal(_) => true
    case _ => false
  }
  
  def isGrammarRule(r: Rule) = !isTerminal(r.left)
  
  def noEpsilon(r: Rule) = r.right match {
    case Nil() => false
    case Cons(_, _) => true
  }
  
  def areGrammarRule(lr: List[Rule]): Boolean = lr match {
    case Nil() => true
    case Cons(r, q) => isGrammarRule(r) && areGrammarRule(q)
  }
  
  def noEpsilons(lr: List[Rule]): Boolean = lr match {
    case Nil() => true
    case Cons(r, q) => noEpsilon(r) && noEpsilons(q)
  }
  
  def isGrammar(g: Grammar) = !isTerminal(g.start) && areGrammarRule(g.rules)
  
  def isReasonableRule(r: List[Symbol], excluded: Symbol): Boolean = r match {
    case Nil() => true
    case Cons(rs, q) if rs == excluded => false
    case Cons(_, q) => isReasonableRule(q, excluded)
  }
  
  def isReasonable(lr: List[Rule]): Boolean = lr match {
    case Nil() => true
    case Cons(r, q) => isReasonableRule(r.right, r.left) && isReasonable(q)
  } 
  
  def allGrammarsAreIdentical(g: Grammar, g2: Grammar) = {
    require(isGrammar(g) && isGrammar(g2) && noEpsilons(g.rules) && noEpsilons(g2.rules) && isReasonable(g.rules) && isReasonable(g2.rules))
    (g == g2 || g.rules == g2.rules)
  } holds
}