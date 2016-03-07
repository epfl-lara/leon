/**
  * Name:     SymbolGrammarRender.scala
  * Creation: 14.01.2016
  * Author:   Mika�l Mayer (mikael.mayer@epfl.ch)
  * Comments: Grammar rendering specifications starting with symbols
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object GrammarRender {
  /** A tagged symbol */
  abstract class Symbol
  /** A tagged non-terminal, used for markovization */
  case class NonTerminal(tag: String, vcontext: List[Symbol], hcontext: List[Symbol]) extends Symbol
  /** A tagged terminal */
  case class Terminal(tag: String) extends Symbol
  
    /** All possible right-hand-side of rules */
  case class Expansion(ls: List[List[Symbol]]) 
  /** A grammar here has a start sequence instead of a start symbol */
  case class Grammar(start: List[Symbol], rules: List[(Symbol, Expansion)])

  def symbol_markov(s: Grammar): String = {
    ???[String]
  } ensuring {
    (res : String) => (s, res) passes {
      case Terminal("foo") =>
        "Tfoo"
      case Terminal("\"'\n\t") =>
        "T\"'\n\t"
      case NonTerminal("foo", Nil(), Nil()) =>
        "Nfoo"
      case NonTerminal("\"'\n\t", Nil(), Nil()) =>
        "N\"'\n\t"
      case NonTerminal("foo", Nil(), Cons(Terminal("foo"), Nil())) =>
        "Nfoo_hTfoo"
      case NonTerminal("foo", Cons(Terminal("foo"), Nil()), Nil()) =>
        "Nfoo_vTfoo"
      case NonTerminal("foo", Nil(), Cons(NonTerminal("foo", Nil(), Nil()), Cons(NonTerminal("foo", Nil(), Nil()), Nil()))) =>
        "Nfoo_hNfoo_Nfoo"
      case NonTerminal("foo", Cons(Terminal("foo"), Nil()), Cons(NonTerminal("foo", Nil(), Nil()), Nil())) =>
        "Nfoo_vTfoo_hNfoo"
      case NonTerminal("foo", Cons(NonTerminal("foo", Nil(), Nil()), Cons(NonTerminal("foo", Nil(), Nil()), Nil())), Nil()) =>
        "Nfoo_vNfoo_Nfoo"
    }
  }
  
  def grammarToString(p : Grammar): String = 
    ???[String] ask p
}