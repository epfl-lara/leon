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
  
  /** Given a grammar, expanding with the first, second or third rule for the symbol should yield the same list each time.
   *  Obviously wrong, but provides meaningful counter-examples. */
  def threeExpansionsIsTheSame(g: Grammar, s: Symbol) = {
    require(isGrammar(g) && noEpsilons(g.rules) && isReasonable(g.rules) && !isTerminal(s))
    val a = expand(g.rules, s, BigInt(0))
    val b = expand(g.rules, s, BigInt(1))
    val c = expand(g.rules, s, BigInt(2))
    a == b && b == c
  } holds

  //////////////////////////////////////////////
  // Non-incremental examples: pure synthesis //
  //////////////////////////////////////////////
  def grammarToString(s : Grammar): String =  ???[String] ask s
}