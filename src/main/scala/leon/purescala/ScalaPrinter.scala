/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Common._
import Trees._
import TypeTrees._
import Definitions._

/** This pretty-printer only print valid scala syntax */
class ScalaPrinter(opts: PrinterOptions, sb: StringBuffer = new StringBuffer) extends PrettyPrinter(opts, sb) {
  import Common._
  import Trees._
  import TypeTrees._
  import Definitions._

  import java.lang.StringBuffer

  override def ppBinary(left: Tree, right: Tree, op: String)(implicit  parent: Option[Tree], lvl: Int) {
    pp(left, parent)
    sb.append(op)
    pp(right, parent)
  }

  // EXPRESSIONS
  // all expressions are printed in-line
  override def pp(tree: Tree, parent: Option[Tree])(implicit lvl: Int): Unit = {
    implicit val p = Some(tree)

    def optParentheses(body: => Unit) {
      val rp = requiresParentheses(tree, parent)
      if (rp) sb.append("(")
      body
      if (rp) sb.append(")")
    }

    def optBraces(body: Int => Unit) {
      val rp = requiresBraces(tree, parent)
      if (rp) {
        sb.append("{\n")
        ind(lvl+1)

        body(lvl+1)

        sb.append("\n")
        ind(lvl)
        sb.append("}\n")
      } else {
        body(lvl)
      }
    }

    var printPos = opts.printPositions

    tree match {
      case LetTuple(ids,d,e) =>
        optBraces { implicit lvl =>
          sb.append("val (" )
          for (((id, tpe), i) <- ids.map(id => (id, id.getType)).zipWithIndex) {
              pp(id, p)
              sb.append(": ")
              pp(tpe, p)
              if (i != ids.size-1) {
                  sb.append(", ")
              }
          }
          sb.append(") = ")
          pp(d, p)
          sb.append("\n")
          ind
          pp(e, p)
          sb.append("\n")
        }

      case Let(b,d,e) =>
        optBraces { implicit lvl =>
          sb.append("val " + b + " = ")
          pp(d, p)
          sb.append("\n")
          ind
          pp(e, p)
          sb.append("\n")
        }

      case LetDef(fd, body) =>
        optBraces { implicit lvl =>
          pp(fd, p)
          sb.append("\n")
          sb.append("\n")
          ind
          pp(body, p)
        }

      case And(exprs)           => optParentheses { ppNary(exprs, "", " && ", "") }
      case Or(exprs)            => optParentheses { ppNary(exprs, "", " || ", "") }
      case Not(Equals(l, r))    => optParentheses { ppBinary(l, r, " != ") }
      case UMinus(expr)         => ppUnary(expr, "-(", ")")
      case Equals(l,r)          => optParentheses { ppBinary(l, r, " == ") }

      case IntLiteral(v)        => sb.append(v)
      case RealLiteral(n,d)		=> sb.append(n+"/"+d)
      case BooleanLiteral(v)    => sb.append(v)
      case StringLiteral(s)     => sb.append("\"" + s + "\"")
      case UnitLiteral()        => sb.append("()")

      /* These two aren't really supported in Scala, but we know how to encode them. */
      case Implies(l,r)         => pp(Or(Not(l), r), p)
      case Iff(l,r)             => optParentheses { ppBinary(l, r, " == ") }

      case Tuple(exprs)         => ppNary(exprs, "(", ", ", ")")
      case TupleSelect(t, i)    =>
        pp(t, p)
        sb.append("._" + i)

      case Plus(l,r)            => optParentheses { ppBinary(l, r, " + ") }
      case Minus(l,r)           => optParentheses { ppBinary(l, r, " - ") }
      case Times(l,r)           => optParentheses { ppBinary(l, r, " * ") }
      case Division(l,r)        => optParentheses { ppBinary(l, r, " / ") }
      case Modulo(l,r)          => optParentheses { ppBinary(l, r, " % ") }
      case LessThan(l,r)        => optParentheses { ppBinary(l, r, " < ") }
      case GreaterThan(l,r)     => optParentheses { ppBinary(l, r, " > ") }
      case LessEquals(l,r)      => optParentheses { ppBinary(l, r, " <= ") }
      case GreaterEquals(l,r)   => optParentheses { ppBinary(l, r, " >= ") }
      case fs @ FiniteSet(rs)        =>
        if (rs.isEmpty) {
          fs.getType match {
            case SetType(b) =>
              sb.append("Set[")
              pp(b, p)
              sb.append("]()")
            case _ =>
              sb.append("Set()")
          }
        } else {
          ppNary(rs, "Set(", ", ", ")")
        }
      case FiniteMultiset(rs)   => ppNary(rs, "{|", ", ", "|}")
      case EmptyMultiset(_)     => sys.error("Not Valid Scala")
      case ElementOfSet(e, s)   => optParentheses { ppBinary(s, e, " contains ") }
      case SetUnion(l,r)        => optParentheses { ppBinary(l, r, " ++ ") }
      case SetDifference(l,r)   => optParentheses { ppBinary(l, r, " -- ") }
      case SetIntersection(l,r) => optParentheses { ppBinary(l, r, " & ") }
      case SetMin(s) =>
        pp(s, p)
        sb.append(".min")
      case SetMax(s) =>
        pp(s, p)
        sb.append(".max")
      case SetCardinality(t) => ppUnary(t, "", ".size")
      case FiniteMap(rs) =>
        sb.append("{")
        val sz = rs.size
        var c = 0
        rs.foreach{case (k, v) => {
          pp(k, p); sb.append(" -> "); pp(v, p); c += 1 ; if(c < sz) sb.append(", ")
        }}
        sb.append("}")

      case MapGet(m,k) =>
        pp(m, p)
        ppNary(Seq(k), "(", ",", ")")

      case MapIsDefinedAt(m,k) => {
        pp(m, p)
        sb.append(".isDefinedAt")
        ppNary(Seq(k), "(", ",", ")")
      }
      case ArrayLength(a) =>
        pp(a, p)
        sb.append(".length")

      case ArrayClone(a) =>
        pp(a, p)
        sb.append(".clone")

      case ArrayFill(size, v) =>
        sb.append("Array.fill(")
        pp(size, p)
        sb.append(")(")
        pp(v, p)
        sb.append(")")

      case ArraySelect(ar, i) =>
        pp(ar, p)
        sb.append("(")
        pp(i, p)
        sb.append(")")

      case ArrayUpdated(ar, i, v) =>
        pp(ar, p)
        sb.append(".updated(")
        pp(i, p)
        sb.append(", ")
        pp(v, p)
        sb.append(")")

      case FiniteArray(exprs) =>
        ppNary(exprs, "Array(", ", ", ")")

      case Distinct(exprs) =>
        sb.append("distinct")
        ppNary(exprs, "(", ", ", ")")
      
      case IfExpr(c, t, e) =>
        optParentheses {
          sb.append("if (")
          pp(c, p)
          sb.append(") {\n")
          ind(lvl+1)
          pp(t, p)(lvl+1)
          sb.append("\n")
          ind(lvl)
          sb.append("} else {\n")
          ind(lvl+1)
          pp(e, p)(lvl+1)
          sb.append("\n")
          ind(lvl)
          sb.append("}")
        }

      case Choose(ids, pred) =>
        optParentheses {
          sb.append("choose { (")
          for (((id, tpe), i) <- ids.map(id => (id, id.getType)).zipWithIndex) {
              pp(id, p)
              sb.append(": ")
              pp(tpe, p)
              if (i != ids.size-1) {
                  sb.append(", ")
              }
          }
          sb.append(") =>\n")
          ind(lvl+1)
          pp(pred, p)(lvl+1)
          sb.append("\n")
          ind(lvl)
          sb.append("}")
        }

      case mex @ MatchExpr(s, csc) => {
        optParentheses {
          pp(s, p)
          sb.append(" match {\n")

          csc.foreach { cs =>
            ind(lvl+1)
            pp(cs, p)(lvl+1)
            sb.append("\n")
          }

          ind(lvl)
          sb.append("}")
        }
      }

      case Not(expr) => sb.append("!"); optParentheses { pp(expr, p) }

      case e @ Error(desc) => {
        sb.append("leon.lang.error[")
        pp(e.getType, p)
        sb.append("](\"" + desc + "\")")
      }

      case (expr: PrettyPrintable) => expr.printWith(this)

      // Definitions
      case Program(id, modules) =>
        ppNary(modules, "", "\n", "")

      case ModuleDef(id, defs) =>
        sb.append("object ")
        pp(id, p)
        sb.append(" {\n")

        var c = 0
        val sz = defs.size

        defs.foreach(df => {
          ind(lvl+1)
          pp(df, p)(lvl+1)
          if(c < sz - 1) {
            sb.append("\n\n")
          }
          c = c + 1
        })

        sb.append("\n")
        ind(lvl)
        sb.append("}\n")

      case vd: ValDef =>
        pp(vd.id, p)
        sb.append(": ")
        pp(vd.tpe, p)

      case fd: FunDef =>
        sb.append("def ")
        pp(fd.id, p)

        if (fd.tparams.nonEmpty) {
          ppNary(fd.tparams, "[", ", ", "]")
        }

        ppNary(fd.params, "(", ", ", ")")

        sb.append(": ")
        pp(fd.returnType, p)
        sb.append(" = {\n")
        ind(lvl+1)

        fd.precondition match {
          case None =>
          case Some(prec) =>
            sb.append("require(")
            pp(prec, p)(lvl+1)
            sb.append(");\n")
            ind(lvl+1)
        }

        fd.body match {
          case Some(body) =>
            pp(body, p)(lvl+1)
          case None =>
            sb.append("???")
        }

        sb.append("\n")
        ind

        fd.postcondition match {
          case None =>
            sb.append("}")

          case Some((id, postc)) =>
            sb.append("} ensuring { ")
            pp(Variable(id), p)
            sb.append(" => ")
            pp(postc, p)
            sb.append(" }")
        }

      case _ =>
        super.pp(tree, parent)(lvl)
        // Parent will already print
        printPos = false
    }

    if (printPos) {
      ppos(tree.getPos)
    }
  }

  private def requiresBraces(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, None) => false
    case (_, Some(_: Definition)) => false
    case (_, Some(_: MatchExpr | _: MatchCase | _: Let | _: LetTuple | _: LetDef)) => false
    case (_, _) => true
  }

  private def precedence(ex: Expr): Int = ex match {
    case (_: ElementOfSet) => 0
    case (_: Or) => 1
    case (_: And) => 3
    case (_: GreaterThan | _: GreaterEquals  | _: LessEquals | _: LessThan) => 4
    case (_: Equals | _: Iff | _: Not) => 5
    case (_: Plus | _: Minus | _: SetUnion| _: SetDifference) => 6
    case (_: Times | _: Division | _: Modulo) => 7
    case _ => 7
  }

  private def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, None) => false
    case (_, Some(_: Definition)) => false
    case (_, Some(_: MatchExpr | _: MatchCase | _: Let | _: LetTuple | _: LetDef | _: IfExpr)) => false
    case (_, Some(_: FunctionInvocation)) => false
    case (ie: IfExpr, _) => true
    case (e1: Expr, Some(e2: Expr)) if precedence(e1) > precedence(e2) => false
    case (_, _) => true
  }
}

object ScalaPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions) = new ScalaPrinter(opts)
}
