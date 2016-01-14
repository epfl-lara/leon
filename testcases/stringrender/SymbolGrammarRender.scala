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
  /** A tagged symbol */
  abstract class Symbol
  /** A tagged non-terminal, used for markovization */
  case class NonTerminal(tag: String, vcontext: List[Symbol], hcontext: List[Symbol]) extends Symbol
  /** A tagged terminal */
  case class Terminal(tag: String) extends Symbol

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
}