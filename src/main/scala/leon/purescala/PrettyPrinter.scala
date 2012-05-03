package leon
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
  private def ppUnary(sb: StringBuffer, expr: Expr, op1: String, op2: String, lvl: Int): StringBuffer = {
    var nsb: StringBuffer = sb
    nsb.append(op1)
    nsb = pp(expr, nsb, lvl)
    nsb.append(op2)
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

  private def ppNary(sb: StringBuffer, exprs: Seq[Expr], pre: String, op: String, post: String, lvl: Int): StringBuffer = {
    var nsb = sb
    nsb.append(pre)
    val sz = exprs.size
    var c = 0

    exprs.foreach(ex => {
      nsb = pp(ex, nsb, lvl) ; c += 1 ; if(c < sz) nsb.append(op)
    })

    nsb.append(post)
    nsb
  }

  private def pp(tree: Expr, sb: StringBuffer, lvl: Int): StringBuffer = tree match {
    case Variable(id) => sb.append(id)
    case DeBruijnIndex(idx) => sb.append("_" + idx)
    case Let(b,d,e) => {
        //pp(e, pp(d, sb.append("(let (" + b + " := "), lvl).append(") in "), lvl).append(")")
      sb.append("(let (" + b + " := ");
      pp(d, sb, lvl)
      sb.append(") in\n")
      ind(sb, lvl+1)
      pp(e, sb, lvl+1)
      sb.append(")")
      sb
    }
    case LetVar(b,d,e) => {
      sb.append("(letvar (" + b + " := ");
      pp(d, sb, lvl)
      sb.append(") in\n")
      ind(sb, lvl+1)
      pp(e, sb, lvl+1)
      sb.append(")")
      sb
    }
    case LetDef(fd,e) => {
      sb.append("\n")
      pp(fd, sb, lvl+1)
      sb.append("\n")
      sb.append("\n")
      ind(sb, lvl)
      pp(e, sb, lvl)
      sb
    }
    case And(exprs) => ppNary(sb, exprs, "(", " \u2227 ", ")", lvl)            // \land
    case Or(exprs) => ppNary(sb, exprs, "(", " \u2228 ", ")", lvl)             // \lor
    case Not(Equals(l, r)) => ppBinary(sb, l, r, " \u2260 ", lvl)    // \neq
    case Iff(l,r) => ppBinary(sb, l, r, " <=> ", lvl)              
    case Implies(l,r) => ppBinary(sb, l, r, " ==> ", lvl)              
    case UMinus(expr) => ppUnary(sb, expr, "-(", ")", lvl)
    case Equals(l,r) => ppBinary(sb, l, r, " == ", lvl)
    case IntLiteral(v) => sb.append(v)
    case BooleanLiteral(v) => sb.append(v)
    case StringLiteral(s) => sb.append("\"" + s + "\"")
    case UnitLiteral => sb.append("()")
    case Block(exprs, last) => {
      sb.append("{\n")
      (exprs :+ last).foreach(e => {
        ind(sb, lvl+1)
        pp(e, sb, lvl+1)
        sb.append("\n")
      })
      ind(sb, lvl)
      sb.append("}\n")
      sb
    }
    case Assignment(lhs, rhs) => ppBinary(sb, lhs.toVariable, rhs, " = ", lvl)
    case wh@While(cond, body) => {
      wh.invariant match {
        case Some(inv) => {
          sb.append("\n")
          ind(sb, lvl)
          sb.append("@invariant: ")
          pp(inv, sb, lvl)
          sb.append("\n")
          ind(sb, lvl)
        }
        case None =>
      }
      sb.append("while(")
      pp(cond, sb, lvl)
      sb.append(")\n")
      ind(sb, lvl+1)
      pp(body, sb, lvl+1)
      sb.append("\n")
    }

    case Tuple(exprs) => ppNary(sb, exprs, "(", ", ", ")", lvl)
    case TupleSelect(t, i) => {
      pp(t, sb, lvl)
      sb.append("._" + i)
      sb
    }

    case e@Epsilon(pred) => {
      var nsb = sb
      nsb.append("epsilon(x" + e.posIntInfo._1 + "_" + e.posIntInfo._2 + ". ")
      nsb = pp(pred, nsb, lvl)
      nsb.append(")")
      nsb
    }

    case OptionSome(a) => {
      var nsb = sb
      nsb.append("Some(")
      nsb = pp(a, nsb, lvl)
      nsb.append(")")
      nsb
    }

    case OptionNone(_) => sb.append("None")

    case CaseClass(cd, args) => {
      var nsb = sb
      nsb.append(cd.id)
      nsb = ppNary(nsb, args, "(", ", ", ")", lvl)
      nsb
    }
    case CaseClassInstanceOf(cd, e) => {
      var nsb = sb
      nsb = pp(e, nsb, lvl)
      nsb.append(".isInstanceOf[" + cd.id + "]")
      nsb
    }
    case CaseClassSelector(_, cc, id) => pp(cc, sb, lvl).append("." + id)
    case FunctionInvocation(fd, args) => {
      var nsb = sb
      nsb.append(fd.id)
      nsb = ppNary(nsb, args, "(", ", ", ")", lvl)
      nsb
    }
    case AnonymousFunction(es, ev) => {
      var nsb = sb
      nsb.append("{")
      es.foreach {
        case (as, res) => 
          nsb = ppNary(nsb, as, "", " ", "", lvl)
          nsb.append(" -> ")
          nsb = pp(res, nsb, lvl)
          nsb.append(", ")
      }
      nsb.append("else -> ")
      nsb = pp(ev, nsb, lvl)
      nsb.append("}")
    }
    case AnonymousFunctionInvocation(id, args) => {
      var nsb = sb
      nsb.append(id)
      nsb = ppNary(nsb, args, "(", ", ", ")", lvl)
      nsb
    }
    case Plus(l,r) => ppBinary(sb, l, r, " + ", lvl)
    case Minus(l,r) => ppBinary(sb, l, r, " - ", lvl)
    case Times(l,r) => ppBinary(sb, l, r, " * ", lvl)
    case Division(l,r) => ppBinary(sb, l, r, " / ", lvl)
    case Modulo(l,r) => ppBinary(sb, l, r, " % ", lvl)
    case LessThan(l,r) => ppBinary(sb, l, r, " < ", lvl)
    case GreaterThan(l,r) => ppBinary(sb, l, r, " > ", lvl)
    case LessEquals(l,r) => ppBinary(sb, l, r, " \u2264 ", lvl)      // \leq
    case GreaterEquals(l,r) => ppBinary(sb, l, r, " \u2265 ", lvl)   // \geq
    case FiniteSet(rs) => ppNary(sb, rs, "{", ", ", "}", lvl)
    case FiniteMultiset(rs) => ppNary(sb, rs, "{|", ", ", "|}", lvl)
    case EmptySet(_) => sb.append("\u2205")                          // Ø
    case EmptyMultiset(_) => sb.append("\u2205")                     // Ø
    case Not(ElementOfSet(s,e)) => ppBinary(sb, s, e, " \u2209 ", lvl) // \notin
    case ElementOfSet(s,e) => ppBinary(sb, s, e, " \u2208 ", lvl)    // \in
    case SubsetOf(l,r) => ppBinary(sb, l, r, " \u2286 ", lvl)        // \subseteq
    case Not(SubsetOf(l,r)) => ppBinary(sb, l, r, " \u2288 ", lvl)        // \notsubseteq
    case SetMin(s) => pp(s, sb, lvl).append(".min")
    case SetMax(s) => pp(s, sb, lvl).append(".max")
    case SetUnion(l,r) => ppBinary(sb, l, r, " \u222A ", lvl)        // \cup
    case MultisetUnion(l,r) => ppBinary(sb, l, r, " \u222A ", lvl)   // \cup
    case MapUnion(l,r) => ppBinary(sb, l, r, " \u222A ", lvl)        // \cup
    case SetDifference(l,r) => ppBinary(sb, l, r, " \\ ", lvl)       
    case MultisetDifference(l,r) => ppBinary(sb, l, r, " \\ ", lvl)       
    case SetIntersection(l,r) => ppBinary(sb, l, r, " \u2229 ", lvl) // \cap
    case MultisetIntersection(l,r) => ppBinary(sb, l, r, " \u2229 ", lvl) // \cap
    case SetCardinality(t) => ppUnary(sb, t, "|", "|", lvl)
    case MultisetCardinality(t) => ppUnary(sb, t, "|", "|", lvl)
    case MultisetPlus(l,r) => ppBinary(sb, l, r, " \u228E ", lvl)    // U+
    case MultisetToSet(e) => pp(e, sb, lvl).append(".toSet")
    case EmptyMap(_,_) => sb.append("{}")
    case SingletonMap(f,t) => ppBinary(sb, f, t, " -> ", lvl)
    case FiniteMap(rs) => ppNary(sb, rs, "{", ", ", "}", lvl)
    case MapGet(m,k) => {
      var nsb = sb
      pp(m, nsb, lvl)
      nsb = ppNary(nsb, Seq(k), "(", ",", ")", lvl)
      nsb
    }
    case MapIsDefinedAt(m,k) => {
      var nsb = sb
      pp(m, nsb, lvl)
      nsb.append(".isDefinedAt")
      nsb = ppNary(nsb, Seq(k), "(", ",", ")", lvl)
      nsb
    }
    case ArrayFill(size, v) => {
      sb.append("Array.fill(")
      pp(size, sb, lvl)
      sb.append(")(")
      pp(v, sb, lvl)
      sb.append(")")
    }
    case ArraySelect(ar, i) => {
      pp(ar, sb, lvl)
      sb.append("(")
      pp(i, sb, lvl)
      sb.append(")")
    }
    case ArrayUpdate(ar, i, v) => {
      pp(ar, sb, lvl)
      sb.append("(")
      pp(i, sb, lvl)
      sb.append(") = ")
      pp(v, sb, lvl)
    }
    case ArrayUpdated(ar, i, v) => {
      pp(ar, sb, lvl)
      sb.append(".updated(")
      pp(i, sb, lvl)
      sb.append(", ")
      pp(v, sb, lvl)
      sb.append(")")
    }

    case Distinct(exprs) => {
      var nsb = sb
      nsb.append("distinct")
      nsb = ppNary(nsb, exprs, "(", ", ", ")", lvl)
      nsb
    }
    
    case IfExpr(c, t, e) => {
      var nsb = sb
      nsb.append("if (")
      nsb = pp(c, nsb, lvl)
      nsb.append(")\n")
      ind(nsb, lvl+1)
      nsb = pp(t, nsb, lvl+1)
      nsb.append("\n")
      ind(nsb, lvl)
      nsb.append("else\n")
      ind(nsb, lvl+1)
      nsb = pp(e, nsb, lvl+1)
      nsb
      //nsb.append(") {\n")
      //ind(nsb, lvl+1)
      //nsb = pp(t, nsb, lvl+1)
      //nsb.append("\n")
      //ind(nsb, lvl)
      //nsb.append("} else {\n")
      //ind(nsb, lvl+1)
      //nsb = pp(e, nsb, lvl+1)
      //nsb.append("\n")
      //ind(nsb, lvl)
      //nsb.append("}")
      //nsb
    }

    case mex @ MatchExpr(s, csc) => {
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
        case TuplePattern(bndr, subPatterns) => {
          bndr.foreach(b => sb.append(b + " @ "))
          sb.append("(")
          subPatterns.init.foreach(p => {
            ppc(sb, p)
            sb.append(", ")
          })
          ppc(sb, subPatterns.last)
          sb.append(")")
        }
        case _ => sb.append("Pattern?")
      }

      var nsb = sb
      nsb == pp(s, nsb, lvl)
      // if(mex.posInfo != "") {
      //   nsb.append(" match@(" + mex.posInfo + ") {\n")
      // } else {
        nsb.append(" match {\n")
      // }

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
    case EpsilonVariable((row, col)) => sb.append("x" + row + "_" + col)
    case Not(expr) => ppUnary(sb, expr, "\u00AC(", ")", lvl)               // \neg

    case e @ Error(desc) => {
      var nsb = sb
      nsb.append("error(\"" + desc + "\")[")
      nsb = pp(e.getType, nsb, lvl)
      nsb.append("]")
      nsb
    }

    case _ => sb.append("Expr?")
  }

  // TYPE TREES
  // all type trees are printed in-line
  private def ppNaryType(sb: StringBuffer, tpes: Seq[TypeTree], pre: String, op: String, post: String, lvl: Int): StringBuffer = {
    var nsb = sb
    nsb.append(pre)
    val sz = tpes.size
    var c = 0

    tpes.foreach(t => {
      nsb = pp(t, nsb, lvl) ; c += 1 ; if(c < sz) nsb.append(op)
    })

    nsb.append(post)
    nsb
  }

  private def pp(tpe: TypeTree, sb: StringBuffer, lvl: Int): StringBuffer = tpe match {
    case Untyped => sb.append("???")
    case UnitType => sb.append("Unit")
    case Int32Type => sb.append("Int")
    case BooleanType => sb.append("Boolean")
    case ArrayType(bt) => pp(bt, sb.append("Array["), lvl).append("]")
    case SetType(bt) => pp(bt, sb.append("Set["), lvl).append("]")
    case MapType(ft,tt) => pp(tt, pp(ft, sb.append("Map["), lvl).append(","), lvl).append("]")
    case MultisetType(bt) => pp(bt, sb.append("Multiset["), lvl).append("]")
    case OptionType(bt) => pp(bt, sb.append("Option["), lvl).append("]")
    case FunctionType(fts, tt) => {
      var nsb = sb
      if (fts.size > 1)
        nsb = ppNaryType(nsb, fts, "(", ", ", ")", lvl)
      else if (fts.size == 1)
        nsb = pp(fts.head, nsb, lvl)
      nsb.append(" => ")
      pp(tt, nsb, lvl)
    }
    case TupleType(tpes) => ppNaryType(sb, tpes, "(", ", ", ")", lvl)
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

      case fd @ FunDef(id, rt, args, body, pre, post) => {
        var nsb = sb

        for(a <- fd.annotations) {
          ind(nsb, lvl)
          nsb.append("@" + a + "\n")
        }

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
        if(body.isDefined)
          pp(body.get, nsb, lvl)
        else
          nsb.append("[unknown function implementation]")
      }

      case _ => sb.append("Defn?")
    }
  }
}
