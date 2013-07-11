/* Copyright 2009-2013 EPFL, Lausanne */

package purescala.z3plugins.bapa

import scala.text.{Document, DocBreak}
import scala.language.implicitConversions

import Document._
import AST._

import scala.sys.error

object PrettyPrinter {

  /* Interface */
  
  def apply(tree: Tree) = writeString(p(tree))


  /* Implementation */
  
  private val indent = 2
  private val docWidth = 80
  
  private def writeString(doc: Document) = {
    val writer = new java.io.StringWriter()
    doc.format(docWidth, writer)
    writer.flush()
    writer.toString
  }
  

  // Helper methods
  private implicit def stringToDoc(s: String): Document = text(s)
  private val nl: Document = DocBreak
  private def g(d: Document) = group(d)
  private def n(d: Document) = nest(indent, d)
  private def gn(d: Document) = g(n(d))
  private def op(sep: Document, d: Document): Document = op(sep, Seq(d))
  private def op(sep: Document, d1: Document, d2: Document): Document = op(sep, Seq(d1, d2))
  private def op(sep: Document, docs: Seq[Document]): Document = docs.toList match {
    case Nil => empty
    case List(d) => sep :: d
    case d :: ds =>
      gn((d :: (ds map {dd => g(sep :: " " :: dd)})) reduceLeft {_ :/: _})
    // n(ds reduceLeft {(doc, di) => g(g(doc :: " " :: sep) :/: di)})
  }
  private def list(docs: Seq[Document]) = docs.toSeq match {
    case Nil => empty
    case Seq(d) => d
    case ds => n(ds reduceLeft {(doc, di) => g(doc :: "," :/: di)})
  }
  private def plist(ds: Seq[Document]) = paren(list(ds))
  private def blist(ds: Seq[Document]) = brace(list(ds))
  private def paren(d: Document): Document = "(" :: d :: ")"
  private def brace(d: Document): Document = "{" :: d :: "}"
  private def block(d: Document): Document = gn("{" :/: d :/: "}")

  // Symbols
  val (_AND, _OR, _NOT, _IFF, _IMPL, _DEF) = ("n", "v", "!", "<=>", "==>", ":=")
  val (_EQ, _NE, _LE, _LT, _GE, _GT) = ("==", "!=", "<=", "<", ">=", ">")
  val (_NEG) = ("-")
  val (_SEQ, _SNE, _SSEQ, _SSNE, _EMPTYSET, _FULLSET, _UNION, _INTER, _COMPL) = ("s==", "!s==", "s<=", "!s<=", "{}", "{full}", "++", "**", "~")

  // Beautify names
  /*
  private var counter = 0
  private val map = new scala.collection.mutable.HashMap[Symbol,String]
  private def lookup(sym: Symbol) = map getOrElse(sym, {
    counter += 1
    val name = sym.typ match {
      case BoolType => "p_" + counter
      case IntType => "t" + counter
      case SetType => "S" + counter
    }
    map(sym) = name
    name
  })
  */

  // print with parens (if necessary)
  private def pp(tree: Tree): Document = tree match {
    case Var(_) | Lit(_) | Op(_, Seq(_)) => p(tree)
    case _ => paren(p(tree))
  }
  
  // print with braces (if necessary)
  private def bp(tree: Tree): Document = tree match {
    case Var(_) | Lit(_) | Op(_, Seq(_)) => p(tree)
    case _ => block(p(tree))
  }

  // print without parens
  private def p(tree: Tree): Document = tree match {
    case Var(sym) => sym.name // lookup(sym)
    case Lit(TrueLit) => "true"
    case Lit(FalseLit) => "false"
    case Lit(EmptySetLit) => _EMPTYSET
    case Lit(FullSetLit) => _FULLSET
    case Lit(IntLit(i)) => i.toString
    case Op(OR, ts) => op(_OR, ts map pp)
    case Op(AND, ts) => op(_AND, ts map pp)
    case Op(NOT, Seq(Op(SETEQ, ts))) => op(_SNE, ts map pp)
    case Op(NOT, Seq(Op(SUBSETEQ, ts))) => op(_SSNE, ts map pp)
    case Op(NOT, Seq(Op(EQ, ts))) => op(_NE, ts map pp)
    case Op(NOT, Seq(Op(LT, ts))) => op(_GE, ts map pp)
    case Op(NOT, Seq(t)) => op(_NOT, pp(t))
    case Op(IFF, ts) => op(_IFF, ts map pp)
    case Op(EQ, ts) => op(_EQ, ts map pp)
    case Op(LT, ts) => op(_LT, ts map pp)
    case Op(SETEQ, ts) => op(_SEQ, ts map pp)
    case Op(SUBSETEQ, ts) => op(_SSEQ, ts map pp)
    case Op(ADD, ts) => op("+", ts map pp)
    case Op(CARD, Seq(t)) => "|" :: pp(t) :: "|"
    case Op(UNION, ts) => op(_UNION, ts map pp)
    case Op(INTER, ts) => op(_INTER, ts map pp)
    case Op(COMPL, Seq(t)) => op(_COMPL, pp(t))
    case Op(op, args) => error("Unhandled Op-tree : Op(" + op + ", #" + args.size + ")")
    case Lit(lit) => error("Unhandled Lit-tree : Lit(" + lit + ")")
    case _ => error("Unhandled tree : " + tree.getClass)
  }
}
