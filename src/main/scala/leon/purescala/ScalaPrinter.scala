package leon.purescala

/** This pretty-printer only print valid scala syntax */
object ScalaPrinter {
  import Common._
  import Trees._
  import TypeTrees._
  import Definitions._

  import java.lang.StringBuffer

  def apply(tree: Expr): String = {
    val retSB = new StringBuffer
    pp(tree, retSB, 0)
    retSB.toString
  }

  def apply(tree: Expr, lvl: Int): String = {
    val retSB = new StringBuffer
    pp(tree, retSB, lvl)
    retSB.toString
  }

  def apply(tpe: TypeTree): String = {
    val retSB = new StringBuffer
    pp(tpe, retSB, 0)
    retSB.toString
  }

  def apply(defn: Definition): String = {
    val retSB = new StringBuffer
    pp(defn, retSB, 0)
    retSB.toString
  }

  private def ind(sb: StringBuffer, lvl: Int) {
    sb.append("  " * lvl)
  }

  // EXPRESSIONS
  // all expressions are printed in-line
  private def ppUnary(sb: StringBuffer, expr: Expr, op1: String, op2: String, lvl: Int) {
    sb.append(op1)
    pp(expr, sb, lvl)
    sb.append(op2)
  }

  private def ppBinary(sb: StringBuffer, left: Expr, right: Expr, op: String, lvl: Int) {
    sb.append("(")
    pp(left, sb, lvl)
    sb.append(op)
    pp(right, sb, lvl)
    sb.append(")")
  }

  private def ppNary(sb: StringBuffer, exprs: Seq[Expr], pre: String, op: String, post: String, lvl: Int) {
    sb.append(pre)
    val sz = exprs.size
    var c = 0

    exprs.foreach(ex => {
      pp(ex, sb, lvl) ; c += 1 ; if(c < sz) sb.append(op)
    })

    sb.append(post)
  }

  private def pp(tree: Expr, sb: StringBuffer, lvl: Int): Unit = tree match {
    case Variable(id) => sb.append(id)
    case DeBruijnIndex(idx) => sys.error("Not Valid Scala")
    case LetTuple(ids,d,e) => {
      sb.append("locally {\n")
      ind(sb, lvl+1)
      sb.append("val (" )
      for (((id, tpe), i) <- ids.map(id => (id, id.getType)).zipWithIndex) {
          sb.append(id.toString+": ")
          pp(tpe, sb, lvl)
          if (i != ids.size-1) {
              sb.append(", ")
          }
      }
      sb.append(") = ")
      pp(d, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl+1)
      pp(e, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl)
      sb.append("}\n")
      ind(sb, lvl)
    }
    case Let(b,d,e) => {
      sb.append("locally {\n")
      ind(sb, lvl+1)
      sb.append("val " + b + " = ")
      pp(d, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl+1)
      pp(e, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl)
      sb.append("}\n")
      ind(sb, lvl)
    }
    case And(exprs) => ppNary(sb, exprs, "(", " && ", ")", lvl)            // \land
    case Or(exprs) => ppNary(sb, exprs, "(", " || ", ")", lvl)             // \lor
    case Not(Equals(l, r)) => ppBinary(sb, l, r, " != ", lvl)    // \neq
    case UMinus(expr) => ppUnary(sb, expr, "-(", ")", lvl)
    case Equals(l,r) => ppBinary(sb, l, r, " == ", lvl)
    case IntLiteral(v) => sb.append(v)
    case BooleanLiteral(v) => sb.append(v)
    case StringLiteral(s) => sb.append("\"" + s + "\"")
    case UnitLiteral => sb.append("()")

    /* These two aren't really supported in Scala, but we know how to encode them. */
    case Implies(l,r) => pp(Or(Not(l), r), sb, lvl)
    case Iff(l,r) => ppBinary(sb, l, r, " == ", lvl)

    case Tuple(exprs) => ppNary(sb, exprs, "(", ", ", ")", lvl)
    case TupleSelect(t, i) => {
      pp(t, sb, lvl)
      sb.append("._" + i)
    }

    case CaseClass(cd, args) => {
      sb.append(cd.id)
      ppNary(sb, args, "(", ", ", ")", lvl)
    }
    case CaseClassInstanceOf(cd, e) => {
      pp(e, sb, lvl)
      sb.append(".isInstanceOf[" + cd.id + "]")
    }
    case CaseClassSelector(_, cc, id) =>
      pp(cc, sb, lvl)
      sb.append("." + id)
    case FunctionInvocation(fd, args) => {
      sb.append(fd.id)
      ppNary(sb, args, "(", ", ", ")", lvl)
    }
    case Plus(l,r) => ppBinary(sb, l, r, " + ", lvl)
    case Minus(l,r) => ppBinary(sb, l, r, " - ", lvl)
    case Times(l,r) => ppBinary(sb, l, r, " * ", lvl)
    case Division(l,r) => ppBinary(sb, l, r, " / ", lvl)
    case Modulo(l,r) => ppBinary(sb, l, r, " % ", lvl)
    case LessThan(l,r) => ppBinary(sb, l, r, " < ", lvl)
    case GreaterThan(l,r) => ppBinary(sb, l, r, " > ", lvl)
    case LessEquals(l,r) => ppBinary(sb, l, r, " <= ", lvl)      // \leq
    case GreaterEquals(l,r) => ppBinary(sb, l, r, " >= ", lvl)   // \geq
    case FiniteSet(rs) => ppNary(sb, rs, "Set(", ", ", ")", lvl)
    case FiniteMultiset(rs) => ppNary(sb, rs, "{|", ", ", "|}", lvl)
    case EmptyMultiset(_) => sys.error("Not Valid Scala")
    case ElementOfSet(e, s) => ppBinary(sb, s, e, " contains ", lvl)
    //case ElementOfSet(s,e) => ppBinary(sb, s, e, " \u2208 ", lvl)    // \in
    //case SubsetOf(l,r) => ppBinary(sb, l, r, " \u2286 ", lvl)        // \subseteq
    //case Not(SubsetOf(l,r)) => ppBinary(sb, l, r, " \u2288 ", lvl)        // \notsubseteq
    case SetMin(s) =>
      pp(s, sb, lvl)
      sb.append(".min")
    case SetMax(s) =>
      pp(s, sb, lvl)
      sb.append(".max")
    case SetUnion(l,r) => ppBinary(sb, l, r, " ++ ", lvl)        // \cup
   // case MultisetUnion(l,r) => ppBinary(sb, l, r, " \u222A ", lvl)   // \cup
   // case MapUnion(l,r) => ppBinary(sb, l, r, " \u222A ", lvl)        // \cup
   case SetDifference(l,r) => ppBinary(sb, l, r, " -- ", lvl)       
   // case MultisetDifference(l,r) => ppBinary(sb, l, r, " \\ ", lvl)       
   case SetIntersection(l,r) => ppBinary(sb, l, r, " & ", lvl) // \cap
   // case MultisetIntersection(l,r) => ppBinary(sb, l, r, " \u2229 ", lvl) // \cap
    case SetCardinality(t) => ppUnary(sb, t, "", ".size", lvl)
   // case MultisetCardinality(t) => ppUnary(sb, t, "|", "|", lvl)
   // case MultisetPlus(l,r) => ppBinary(sb, l, r, " \u228E ", lvl)    // U+
   // case MultisetToSet(e) => pp(e, sb, lvl).append(".toSet")
    case FiniteMap(rs) => {
      sb.append("{")
      val sz = rs.size
      var c = 0
      rs.foreach{case (k, v) => {
        pp(k, sb, lvl); sb.append(" -> "); pp(v, sb, lvl); c += 1 ; if(c < sz) sb.append(", ")
      }}
      sb.append("}")
    }
    case MapGet(m,k) => {
      pp(m, sb, lvl)
      ppNary(sb, Seq(k), "(", ",", ")", lvl)
    }
    case MapIsDefinedAt(m,k) => {
      pp(m, sb, lvl)
      sb.append(".isDefinedAt")
      ppNary(sb, Seq(k), "(", ",", ")", lvl)
    }
    case ArrayLength(a) => {
      pp(a, sb, lvl)
      sb.append(".length")
    }
    case ArrayClone(a) => {
      pp(a, sb, lvl)
      sb.append(".clone")
    }
    case ArrayFill(size, v) => {
      sb.append("Array.fill(")
      pp(size, sb, lvl)
      sb.append(")(")
      pp(v, sb, lvl)
      sb.append(")")
    }
    case ArrayMake(v) => sys.error("Not Scala Code")
    case ArraySelect(ar, i) => {
      pp(ar, sb, lvl)
      sb.append("(")
      pp(i, sb, lvl)
      sb.append(")")
    }
    case ArrayUpdated(ar, i, v) => {
      pp(ar, sb, lvl)
      sb.append(".updated(")
      pp(i, sb, lvl)
      sb.append(", ")
      pp(v, sb, lvl)
      sb.append(")")
    }
    case FiniteArray(exprs) => {
      ppNary(sb, exprs, "Array(", ", ", ")", lvl)
    }

    case Distinct(exprs) => {
      sb.append("distinct")
      ppNary(sb, exprs, "(", ", ", ")", lvl)
    }
    
    case IfExpr(c, t, e) => {
      sb.append("if (")
      pp(c, sb, lvl)
      sb.append(") {\n")
      ind(sb, lvl+1)
      pp(t, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl)
      sb.append("} else {\n")
      ind(sb, lvl+1)
      pp(e, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl)
      sb.append("}")
    }

    case Choose(ids, pred) => {
      sb.append("(choose { (")
      for (((id, tpe), i) <- ids.map(id => (id, id.getType)).zipWithIndex) {
          sb.append(id.toString+": ")
          pp(tpe, sb, lvl)
          if (i != ids.size-1) {
              sb.append(", ")
          }
      }
      sb.append(") =>\n")
      ind(sb, lvl+1)
      pp(pred, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl)
      sb.append("})")
    }

    case mex @ MatchExpr(s, csc) => {
      def ppc(sb: StringBuffer, p: Pattern): Unit = p match {
        //case InstanceOfPattern(None,     ctd) =>
        //case InstanceOfPattern(Some(id), ctd) =>
        case CaseClassPattern(bndr,     ccd, subps) => {
          bndr.foreach(b => sb.append(b + " @ "))
          sb.append(ccd.id).append("(")
          var c = 0
          val sz = subps.size
          subps.foreach(sp => {
            ppc(sb, sp)
            if(c < sz - 1)
              sb.append(", ")
            c = c + 1
          })
          sb.append(")")
        }
        case WildcardPattern(None)     => sb.append("_")
        case WildcardPattern(Some(id)) => sb.append(id)
        case InstanceOfPattern(bndr, ccd) => {
          bndr.foreach(b => sb.append(b + " : "))
          sb.append(ccd.id)
        }
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

      sb.append("(")
      pp(s, sb, lvl)
      // if(mex.posInfo != "") {
      //   sb.append(" match@(" + mex.posInfo + ") {\n")
      // } else {
        sb.append(" match {\n")
      // }

      csc.foreach(cs => {
        ind(sb, lvl+1)
        sb.append("case ")
        ppc(sb, cs.pattern)
        cs.theGuard.foreach(g => {
          sb.append(" if ")
          pp(g, sb, lvl+1)
        })
        sb.append(" =>\n")
        ind(sb, lvl+2)
        pp(cs.rhs, sb, lvl+2)
        sb.append("\n")
      })
      ind(sb, lvl)
      sb.append("}")
      sb.append(")")
    }

    case ResultVariable() => sb.append("res")
    case Not(expr) => ppUnary(sb, expr, "!(", ")", lvl)               // \neg

    case e @ Error(desc) => {
      sb.append("leon.Utils.error[")
      pp(e.getType, sb, lvl)
      sb.append("](\"" + desc + "\")")
    }

    case (expr: ScalaPrintable) => expr.ppScala(sb, lvl, pp, pp, pp)
    case _ => sb.append("Expr?")
  }

  // TYPE TREES
  // all type trees are printed in-line
  private def ppNaryType(sb: StringBuffer, tpes: Seq[TypeTree], pre: String, op: String, post: String, lvl: Int) = {
    sb.append(pre)
    val sz = tpes.size
    var c = 0

    tpes.foreach(t => {
      pp(t, sb, lvl) ; c += 1 ; if(c < sz) sb.append(op)
    })

    sb.append(post)
  }

  private def pp(tpe: TypeTree, sb: StringBuffer, lvl: Int): Unit = tpe match {
    case Untyped => sb.append("???")
    case UnitType => sb.append("Unit")
    case Int32Type => sb.append("Int")
    case BooleanType => sb.append("Boolean")
    case ArrayType(bt) =>
      sb.append("Array[")
      pp(bt, sb, lvl)
      sb.append("]")
    case SetType(bt) =>
      sb.append("Set[")
      pp(bt, sb, lvl)
      sb.append("]")
    case MapType(ft,tt) =>
      sb.append("Map[")
      pp(ft, sb, lvl)
      sb.append(",")
      pp(tt, sb, lvl)
      sb.append("]")
    case MultisetType(bt) =>
      sb.append("Multiset[")
      pp(bt, sb, lvl)
      sb.append("]")
    case TupleType(tpes) => ppNaryType(sb, tpes, "(", ", ", ")", lvl)
    case c: ClassType => sb.append(c.classDef.id)
    case _ => sb.append("Type?")
  }

  // DEFINITIONS
  // all definitions are printed with an end-of-line
  private def pp(defn: Definition, sb: StringBuffer, lvl: Int): Unit = {

    defn match {
      case Program(id, mainObj) => {
        assert(lvl == 0)
        pp(mainObj, sb, lvl)
      }

      case ObjectDef(id, defs, invs) => {
        ind(sb, lvl)
        sb.append("object ")
        sb.append(id)
        sb.append(" {\n")

        var c = 0
        val sz = defs.size

        defs.foreach(df => {
          pp(df, sb, lvl+1)
          if(c < sz - 1) {
            sb.append("\n\n")
          }
          c = c + 1
        })

        sb.append("\n")
        ind(sb, lvl)
        sb.append("}\n")
      }

      case AbstractClassDef(id, parent) => {
        ind(sb, lvl)
        sb.append("sealed abstract class ")
        sb.append(id)
        parent.foreach(p => sb.append(" extends " + p.id))
        sb
      }

      case CaseClassDef(id, parent, varDecls) => {
        ind(sb, lvl)
        sb.append("case class ")
        sb.append(id)
        sb.append("(")
        var c = 0
        val sz = varDecls.size

        varDecls.foreach(vd => {
          sb.append(vd.id)
          sb.append(": ")
          pp(vd.tpe, sb, lvl)
          if(c < sz - 1) {
            sb.append(", ")
          }
          c = c + 1
        })
        sb.append(")")
        parent.foreach(p => sb.append(" extends " + p.id))
        sb
      }

      case fd @ FunDef(id, rt, args, body, pre, post) => {

        //for(a <- fd.annotations) {
        //  ind(sb, lvl)
        //  sb.append("@" + a + "\n")
        //}

        ind(sb, lvl)
        sb.append("def ")
        sb.append(id)
        sb.append("(")

        val sz = args.size
        var c = 0
        
        args.foreach(arg => {
          sb.append(arg.id)
          sb.append(" : ")
          pp(arg.tpe, sb, lvl)

          if(c < sz - 1) {
            sb.append(", ")
          }
          c = c + 1
        })

        sb.append(") : ")
        pp(rt, sb, lvl)
        sb.append(" = (")
        if(body.isDefined) {
          pre match {
            case None => pp(body.get, sb, lvl)
            case Some(prec) => {
              sb.append("{\n")
              ind(sb, lvl+1)
              sb.append("require(")
              pp(prec, sb, lvl+1)
              sb.append(")\n")
              pp(body.get, sb, lvl)
              sb.append("\n")
              ind(sb, lvl)
              sb.append("}")
            }
          }
        } else
          sb.append("[unknown function implementation]")

        post match {
          case None => {
            sb.append(")")
          }
          case Some(postc) => {
            val res = Variable(FreshIdentifier("res", true).setType(fd.returnType))

            val newPost = TreeOps.replace(Map(ResultVariable() -> res), postc)

            sb.append(" ensuring(")
            pp(res, sb, lvl)
            sb.append(" => ") //TODO, not very general solution...
            pp(newPost, sb, lvl)
            sb.append("))")
          }
        }

        sb
      }

      case _ => sb.append("Defn?")
    }
  }

  trait ScalaPrintable {
    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer
  }
}
