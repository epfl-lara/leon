package purescala


/** This pretty-printer uses Unicode for some operators, to make sure we
 * distinguish PureScala from "real" Scala (and also because it's cute). */
object PrettyPrinter {
  import Common._
  import Trees._
  import TypeTrees._
  import Definitions._

  import java.lang.StringBuffer

  def apply(tree: Expr): String = {
    val retSB = pp(tree, new StringBuffer, 0)
    retSB.toString
  }

  def apply(tpe: TypeTree): String = {
    val retSB = pp(tpe, new StringBuffer, 0)
    retSB.toString
  }

  def apply(defn: Definition): String = {
    val retSB = pp(defn, new StringBuffer, 0)
    retSB.toString
  }

  private def ind(sb: StringBuffer, lvl: Int) : StringBuffer = {
      sb.append("  " * lvl)
      sb
  }

  // EXPRESSIONS
  // all expressions are printed in-line
  private def ppUnary(sb: StringBuffer, expr: Expr, op: String, lvl: Int): StringBuffer = {
    var nsb: StringBuffer = sb
    nsb.append(op)
    nsb.append("(")
    nsb = pp(expr, nsb, lvl)
    nsb.append(")")
    nsb
  }

  private def ppBinary(sb: StringBuffer, left: Expr, right: Expr, op: String, lvl: Int): StringBuffer = {
    var nsb: StringBuffer = sb
    nsb.append("(")
    nsb = pp(left, nsb, lvl)
    nsb.append(op)
    nsb = pp(right, nsb, lvl)
    nsb.append(")")
    nsb
  }

  private def ppNary(sb: StringBuffer, exprs: Seq[Expr], op: String, lvl: Int): StringBuffer = {
    var nsb = sb
    nsb.append("(")
    val sz = exprs.size
    var c = 0

    exprs.foreach(ex => {
      nsb = pp(ex, nsb, lvl) ; c += 1 ; if(c < sz) nsb.append(op)
    })

    nsb.append(")")
    nsb
  }

  private def pp(tree: Expr, sb: StringBuffer, lvl: Int): StringBuffer = tree match {
    case Variable(id) => sb.append(id)
    case And(exprs) => ppNary(sb, exprs, " \u2227 ", lvl)            // \land
    case Or(exprs) => ppNary(sb, exprs, " \u2228 ", lvl)             // \lor
    case Not(Equals(l, r)) => ppBinary(sb, l, r, " \u2260 ", lvl)    // \neq
    case Not(expr) => ppUnary(sb, expr, "\u00AC", lvl)               // \neg
    case UMinus(expr) => ppUnary(sb, expr, "-", lvl)
    case Equals(l,r) => ppBinary(sb, l, r, " == ", lvl)
    case IntLiteral(v) => sb.append(v)
    case BooleanLiteral(v) => sb.append(v)
    case StringLiteral(s) => sb.append("\"" + s + "\"")
    case CaseClass(ct, args) => {
      var nsb = sb
      nsb.append(ct.id)
      nsb = ppNary(nsb, args, ", ", lvl)
      nsb
    }
    case CaseClassSelector(cc, id) => pp(cc, sb, lvl).append("." + id)
    case FunctionInvocation(fd, args) => {
      var nsb = sb
      nsb.append(fd.id)
      nsb = ppNary(nsb, args, ", ", lvl)
      nsb
    }
    case Plus(l,r) => ppBinary(sb, l, r, " + ", lvl)
    case Minus(l,r) => ppBinary(sb, l, r, " - ", lvl)
    case Times(l,r) => ppBinary(sb, l, r, " * ", lvl)
    case Division(l,r) => ppBinary(sb, l, r, " / ", lvl)
    case LessThan(l,r) => ppBinary(sb, l, r, " < ", lvl)
    case GreaterThan(l,r) => ppBinary(sb, l, r, " > ", lvl)
    case LessEquals(l,r) => ppBinary(sb, l, r, " \u2264 ", lvl)      // \leq
    case GreaterEquals(l,r) => ppBinary(sb, l, r, " \u2265 ", lvl)   // \geq
    
    case IfExpr(c, t, e) => {
      var nsb = sb
      nsb.append("if (")
      nsb = pp(c, nsb, lvl)
      nsb.append(") {\n")
      ind(nsb, lvl+1)
      nsb = pp(t, nsb, lvl+1)
      nsb.append("\n")
      ind(nsb, lvl)
      nsb.append("} else {\n")
      ind(nsb, lvl+1)
      nsb = pp(e, nsb, lvl+1)
      nsb.append("\n")
      ind(nsb, lvl)
      nsb.append("}")
      nsb
    }

    case MatchExpr(s, csc) => {
      def ppc(sb: StringBuffer, p: Pattern): StringBuffer = p match {
        //case InstanceOfPattern(None,     ctd) =>
        //case InstanceOfPattern(Some(id), ctd) =>
        case CaseClassPattern(bndr,     ccd, subps) => {
          var nsb = sb
          bndr.foreach(b => nsb.append(b + " @ "))
          nsb.append(ccd.id).append("(")
          var c = 0
          val sz = subps.size
          subps.foreach(sp => {
            nsb = ppc(nsb, sp)
            if(c < sz - 1)
              nsb.append(", ")
            c = c + 1
          })
          nsb.append(")")
        }
        case WildcardPattern(None)     => sb.append("_")
        case WildcardPattern(Some(id)) => sb.append(id)
        case _ => sb.append("Pattern?")
      }

      var nsb = sb
      nsb == pp(s, nsb, lvl)
      nsb.append(" match {\n")

      csc.foreach(cs => {
        ind(nsb, lvl+1)
        nsb.append("case ")
        nsb = ppc(nsb, cs.pattern)
        cs.theGuard.foreach(g => {
          nsb.append(" if ")
          nsb = pp(g, nsb, lvl+1)
        })
        nsb.append(" => ")
        nsb = pp(cs.rhs, nsb, lvl+1)
        nsb.append("\n")
      })
      ind(nsb, lvl).append("}")
      nsb
    }

    case ResultVariable() => sb.append("#res")

    case _ => sb.append("Expr?")
  }

  // TYPE TREES
  // all type trees are printed in-line
  private def pp(tpe: TypeTree, sb: StringBuffer, lvl: Int): StringBuffer = tpe match {
    case NoType => sb.append("???")
    case Int32Type => sb.append("Int")
    case BooleanType => sb.append("Boolean")
    case SetType(bt) => pp(bt, sb.append("Set["), lvl).append("]")
    case c: ClassType => sb.append(c.classDef.id)
    case _ => sb.append("Type?")
  }

  // DEFINITIONS
  // all definitions are printed with an end-of-line
  private def pp(defn: Definition, sb: StringBuffer, lvl: Int): StringBuffer = {

    defn match {
      case Program(id, mainObj) => {
        assert(lvl == 0)
        sb.append("package ")
        sb.append(id)
        sb.append(" {\n")
        pp(mainObj, sb, lvl+1).append("}\n")
      }

      case ObjectDef(id, defs, invs) => {
        var nsb = sb
        ind(nsb, lvl)
        nsb.append("object ")
        nsb.append(id)
        nsb.append(" {\n")

        var c = 0
        val sz = defs.size

        defs.foreach(df => {
          nsb = pp(df, nsb, lvl+1)
          if(c < sz - 1) {
            nsb.append("\n\n")
          }
          c = c + 1
        })

        nsb.append("\n")
        ind(nsb, lvl).append("}\n")
      }

      case AbstractClassDef(id, parent) => {
        var nsb = sb
        ind(nsb, lvl)
        nsb.append("sealed abstract class ")
        nsb.append(id)
        parent.foreach(p => nsb.append(" extends " + p.id))
        nsb
      }

      case CaseClassDef(id, parent, varDecls) => {
        var nsb = sb
        ind(nsb, lvl)
        nsb.append("case class ")
        nsb.append(id)
        nsb.append("(")
        var c = 0
        val sz = varDecls.size

        varDecls.foreach(vd => {
          nsb.append(vd.id)
          nsb.append(": ")
          nsb = pp(vd.tpe, nsb, lvl)
          if(c < sz - 1) {
            nsb.append(", ")
          }
          c = c + 1
        })
        nsb.append(")")
        parent.foreach(p => nsb.append(" extends " + p.id))
        nsb
      }

      case FunDef(id, rt, args, body, pre, post) => {
        var nsb = sb

        pre.foreach(prec => {
          ind(nsb, lvl)
          nsb.append("@pre : ")
          nsb = pp(prec, nsb, lvl)
          nsb.append("\n")
        })

        post.foreach(postc => {
          ind(nsb, lvl)
          nsb.append("@post: ")
          nsb = pp(postc, nsb, lvl)
          nsb.append("\n")
        })

        ind(nsb, lvl)
        nsb.append("def ")
        nsb.append(id)
        nsb.append("(")

        val sz = args.size
        var c = 0
        
        args.foreach(arg => {
          nsb.append(arg.id)
          nsb.append(" : ")
          nsb = pp(arg.tpe, nsb, lvl)

          if(c < sz - 1) {
            nsb.append(", ")
          }
          c = c + 1
        })

        nsb.append(") : ")
        nsb = pp(rt, nsb, lvl)
        nsb.append(" = ")
        pp(body, nsb, lvl)
      }

      case _ => sb.append("Defn?")
    }
  }
}
