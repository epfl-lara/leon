package orderedsets

import scala.text.{Document, DocBreak}
import Document._

import purescala.Trees._
import purescala.Common.Identifier

object RPrettyPrinter {
  def apply(expr: Expr) = rpp(expr)

  def rpp(expr: Expr) = writeString(pp(expr))

  private val indent = 2
  private val docWidth = 80

  private def writeString(doc: Document) = {
    val writer = new java.io.StringWriter()
    doc.format(docWidth, writer)
    writer.flush()
    writer.toString
  }


  // Helper methods
  private val line: Document = DocBreak

  private def paren(d: Document): Document =
    group("(" :: nest(indent, d) :: ")")

  private def brace(d: Document): Document =
    group("{" :: nest(indent, d) :: "}")

  private def block(d: Document): Document =
    group("{" :: line :: nest(indent, d) :: line :: "}")

  private def repsep(doc: Seq[Document], sep: Document): Document =
    if (doc isEmpty) empty else
      doc.reduceLeft {(rest, d) => rest :: sep :: d}

  private def ppUnary(expr: Expr, sep: Document) =
    paren(sep :/: pp(expr))

  private def ppBinary(left: Expr, right: Expr, sep: Document) =
    paren(pp(left) :/: sep :/: pp(right))

  private def ppVarary(exprs: Seq[Expr], sep: Document) =
    paren(repsep(exprs map pp, sep))

  private def ppVararyDoc(exprs: Seq[Document], sep: Document) =
    paren(repsep(exprs, sep))

  private def ppVararyBrace(exprs: Seq[Expr], sep: Document) =
    brace(repsep(exprs map pp, sep))


  val (_AND, _OR, _NOT, _IFF, _IMPL, _EQ, _NE) =
  (" n ", " v ", "!", "<=>", "==>", "==", "!=")

  val (_LE, _LT, _GE, _GT) = ("<=", "<", ">=", ">")

  val (_NEG) = ("-")

  val (_SEQ, _SNE, _EMPTYSET, _UNION, _INTER, _MINUS, _INF, _SUP) =
  ("=S=", "!=S=", "{}", "++", "**", "--", ".min", ".max")


  private def pp(expr: Expr): Document = expr match {
    case Variable(id) => id
    case Let(b, d, e) => paren("let" :/: b.toString :/: ":=" :/: pp(d) :/: "in" :/: pp(e))
    case And(es) => ppVarary(es, _AND :: line)
    case Or(es) => ppVarary(es, _OR)
    case Not(Equals(l, r)) => ppBinary(l, r, _NE)
    case Not(SetEquals(l, r)) => ppBinary(l, r, _SNE)
    case Not(e) => ppUnary(e, _NOT)
    case Iff(l, r) => ppBinary(l, r, _IFF)
    case Implies(l, r) => ppBinary(l, r, _IMPL)
    case UMinus(e) => ppUnary(e, _NEG)
    case SetEquals(l, r) => ppBinary(l, r, _SEQ)
    case Equals(l, r) => ppBinary(l, r, _EQ)
    case IntLiteral(v) => v
    case BooleanLiteral(v) => text(v toString)
    case StringLiteral(s) => "\"" :: s :: "\""
    case CaseClass(ct, args) => ct.id :: ppVarary(args, ",")
    case CaseClassSelector(cc, id) => pp(cc) :: "." :: id
    case FunctionInvocation(fd, args) => fd.id :: ppVarary(args, ",")

    case Plus(l, r) => ppBinary(l, r, "+")
    case Minus(l, r) => ppBinary(l, r, "-")
    case Times(l, r) => ppBinary(l, r, "*")
    case Division(l, r) => ppBinary(l, r, "/")
    case LessThan(l, r) => ppBinary(l, r, _LT)
    case GreaterThan(l, r) => ppBinary(l, r, _GT)
    case LessEquals(l, r) => ppBinary(l, r, _LE)
    case GreaterEquals(l, r) => ppBinary(l, r, _GE)
    case FiniteSet(rs) => ppVararyBrace(rs, ", ")
    case EmptySet(_) => _EMPTYSET
    case SetMin(s) => pp(s) :: _INF
    case SetMax(s) => pp(s) :: _SUP
    case SetUnion(l, r) => ppBinary(l, r, _UNION)
    case SetDifference(l, r) => ppBinary(l, r, _MINUS)
    case SetIntersection(l, r) => ppBinary(l, r, _INTER)
    case SetCardinality(t) => "|" :: pp(t) :: "|"

    case IfExpr(c, t, e) => paren(
      group("if" :/: paren(pp(c))) :/:
              group("then" :/: block(pp(t))) :/:
              group("else" :/: block(pp(e)))
      )
    case MatchExpr(s, cases) =>
      def ppc(p: Pattern): Document = p match {
      //case InstanceOfPattern(None,     ctd) =>
      //case InstanceOfPattern(Some(id), ctd) =>
        case CaseClassPattern(None, ccd, subps) =>
          ccd.id :: ppVararyDoc(subps map ppc, ",")
        case CaseClassPattern(Some(bind), ccd, subps) =>
          bind :/: "@" :/: ccd.id :: ppVararyDoc(subps map ppc, ",")
        case WildcardPattern(None) => "_"
        case WildcardPattern(Some(id)) => id
        case _ => "Pattern?"
      }
      def ppguard(opt: Option[Expr]): Document = opt match {
        case None => "=>"
        case Some(ex) => "if" :/: pp(ex) :/: "=>"
      }
      pp(s) :/: "match" :/: brace(
        (cases foldLeft (empty: Document)) {
          (doc, mc) =>
            doc :/: line :/: "case" :/: ppc(mc.pattern) :/: ppguard(mc.theGuard)
        }
        )
    case ResultVariable() => "#res"
    case _ => "Expr?"
  }

  private implicit def stringToDoc(s: String): Document = text(s)

  private implicit def intToDoc(i: Int): Document = text(i.toString)

  private implicit def identToDoc(id: Identifier): Document = text(id.toString)
}

