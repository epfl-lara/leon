package orderedsets

import scala.text.Document
import Document._
import Primitives._
import scala.util.parsing.input.Positional

object AST {
  implicit def sym2prop(s: Symbol): PropVar =
    if (s.isBool) PropVar(s)
    else error("Bad type for PropVar : " + s.tpe)

  implicit def sym2term(s: Symbol): TermVar =
    if (s.isInt || s.isSet) TermVar(s)
    else error("Bad type for TermVar : " + s.tpe)

  implicit def int2term(i: Int): Term = Lit(IntLit(i))

  val emptyset = Lit(EmptySetLit)
  val fullset = Lit(FullSetLit)
  val zero = Lit(IntLit(0))
  val one = Lit(IntLit(1))


  sealed abstract class Formula extends Positional {
    def print {Printer print (Printer toDocument this)}
    override def toString = {Printer printStr (Printer toDocument this)}

    def size = ASTUtil sizeOf this

    def &&(form: Formula) = And(List(this, form))

    def &&(forms: Seq[Formula]) = And(this :: forms.toList)

    def ||(form: Formula, forms: Formula*) = Or(this :: form :: forms.toList)

    def implies(form: Formula) = !this || form

    def unary_! = Not(this)
  }
  case object True extends Formula
  case object False extends Formula
  case class PropVar(sym: Symbol) extends Formula
  case class Not(formula: Formula) extends Formula
  case class And(formulas: List[Formula]) extends Formula
  case class Or(formulas: List[Formula]) extends Formula
  case class Predicate(comp: Logical, terms: List[Term]) extends Formula

  sealed abstract class Term extends Positional {
    def print {Printer print (Printer toDocument this)}
    override def toString = {Printer printStr (Printer toDocument this)}

    def size = ASTUtil sizeOf this

    def singleton = Op(SINGLETON, List(this))

    def <(term: Term) = Predicate(LT, List(this, term))

    def <=(term: Term) = Predicate(LE, List(this, term))

    def ===(term: Term) = Predicate(EQ, List(this, term))

    def =!=(term: Term) = Predicate(NE, List(this, term))

    def >(term: Term) = Predicate(GT, List(this, term))

    def >=(term: Term) = Predicate(GE, List(this, term))

    def seq(term: Term) = Predicate(SEQ, List(this, term))

    def slt(term: Term) = Predicate(SLT, List(this, term))

    def selem(term: Term) = Predicate(SELEM, List(this, term))

    def subseteq(term: Term) = Predicate(SUBSETEQ, List(this, term))

    def +(term: Term, terms: Term*) = Op(ADD, this :: term :: terms.toList)

    def -(term: Term) = Op(SUB, List(this, term))

    def *(term: Term, terms: Term*) = Op(MUL, this :: term :: terms.toList)

    def ++(term: Term) = Op(UNION, List(this, term))

    def ++(terms: Seq[Term]) = Op(UNION, this :: terms.toList)

    def **(term: Term) = Op(INTER, List(this, term))

    def --(term: Term) = Op(INTER, List(this, ~term))

    def lrange(from: Term, to: Term) = Op(LRANGE, List(from, to, this))

    def take(term: Term) = Op(TAKE, List(term, this))

    def card = Op(CARD, List(this))

    def sup = Op(SUP, List(this))

    def inf = Op(INF, List(this))

    def unary_~ = Op(COMPL, List(this))
    //    def compl = Op(COMPL, List(this))
  }

  case class TermVar(sym: Symbol) extends Term
  case class Lit(value: Literal) extends Term
  case class Op(op: NonLogical, terms: List[Term]) extends Term


  /**Pretty printer **/

  private object Printer {
    private implicit def stringToDoc(s: String): Document = text(s)

    private implicit def intToDoc(i: Int): Document = text(i.toString)

    // Helper methods
    def paren(d: Document): Document =
      group("(" :: nest(2, d) :: ")")

    def toDocument(f: Formula): Document = f match {
      case True => "true"
      case False => "false"
      case PropVar(name) => name toString
      case Not(f@Predicate(_, _)) => /*"\u00AC"*/ "!" :/: paren(toDocument(f))
      case Not(f) => /*"\u00AC"*/ "!" :/: toDocument(f)
      case And(fs) =>
        //        paren( repsep(fs map toDocument, "\u2227") )
        paren(repsep(fs map toDocument, "n"))
      case Or(fs) =>
        //        paren( repsep(fs map toDocument, "\u2228") )
        paren(repsep(fs map toDocument, "v"))
      case Predicate(op, t :: Nil) =>
        op.toString :/: paren(toDocument(t))
      case Predicate(op, ts) =>
        paren(repsep(ts map toDocument, op toString))
    }

    def toDocument(f: Term): Document = f match {
      case TermVar(name) => name toString
      case Lit(EmptySetLit) => "{}"
      case Lit(FullSetLit) => "{ALL}"
      case Lit(IntLit(value)) => value
      case Op(op, t :: Nil) =>
        op.toString :/: toDocument(t)
      case Op(op@(LRANGE | TAKE), ts) =>
        op.toString :/: paren(repsep(ts map toDocument, ","))
      case Op(ITE(f), List(t, s)) =>
        nest(2, group("if" :/: toDocument(f)) :/: group("then" :/: toDocument(t)) :/: group("else" :/: toDocument(s)))
      case Op(op, ts) =>
        paren(repsep(ts map toDocument, op toString))
    }

    def repsep(doc: List[Document], sep: Document): Document =
      if (doc isEmpty) empty else
        doc.reduceLeft {(rest, d) => rest :/: group(sep :/: d)}

    def print(doc: Document) {
      val writer = new java.io.PrintWriter(System.out)
      doc.format(50, writer)
      writer.println()
      writer.flush()
    }
    
    def printStr(doc: Document) = {
      val writer = new java.io.StringWriter()
      doc.format(50, writer)
      writer.flush()
      writer.toString
    }
  }

}
