/* Copyright 2009-2013 EPFL, Lausanne */
package leon
package purescala

import Common._
import Trees._
import TypeTrees._
import Definitions._

/** This pretty-printer only print valid scala syntax */
class ScalaPrinter(sb: StringBuffer = new StringBuffer) extends PrettyPrinter(sb) {
  import Common._
  import Trees._
  import TypeTrees._
  import Definitions._

  import java.lang.StringBuffer

  // EXPRESSIONS
  // all expressions are printed in-line
  override def pp(tree: Expr, lvl: Int): Unit = tree match {
    case Variable(id) => sb.append(id)
    case DeBruijnIndex(idx) => sys.error("Not Valid Scala")
    case LetTuple(ids,d,e) =>
      sb.append("locally {\n")
      ind(lvl+1)
      sb.append("val (" )
      for (((id, tpe), i) <- ids.map(id => (id, id.getType)).zipWithIndex) {
          sb.append(id.toString+": ")
          pp(tpe, lvl)
          if (i != ids.size-1) {
              sb.append(", ")
          }
      }
      sb.append(") = ")
      pp(d, lvl+1)
      sb.append("\n")
      ind(lvl+1)
      pp(e, lvl+1)
      sb.append("\n")
      ind(lvl)
      sb.append("}\n")
      ind(lvl)

    case Let(b,d,e) =>
      sb.append("locally {\n")
      ind(lvl+1)
      sb.append("val " + b + " = ")
      pp(d, lvl+1)
      sb.append("\n")
      ind(lvl+1)
      pp(e, lvl+1)
      sb.append("\n")
      ind(lvl)
      sb.append("}\n")
      ind(lvl)

    case LetDef(fd, body) =>
      sb.append("{\n")
      pp(fd, lvl+1)
      sb.append("\n")
      sb.append("\n")
      ind(lvl)
      pp(body, lvl)
      sb.append("}\n")

    case And(exprs) => ppNary(exprs, "(", " && ", ")", lvl)            // \land
    case Or(exprs) => ppNary(exprs, "(", " || ", ")", lvl)             // \lor
    case Not(Equals(l, r)) => ppBinary(l, r, " != ", lvl)    // \neq
    case UMinus(expr) => ppUnary(expr, "-(", ")", lvl)
    case Equals(l,r) => ppBinary(l, r, " == ", lvl)

    case IntLiteral(v) => sb.append(v)
    case BooleanLiteral(v) => sb.append(v)
    case StringLiteral(s) => sb.append("\"" + s + "\"")
    case UnitLiteral => sb.append("()")

    /* These two aren't really supported in Scala, but we know how to encode them. */
    case Implies(l,r) => pp(Or(Not(l), r), lvl)
    case Iff(l,r) => ppBinary(l, r, " == ", lvl)

    case Tuple(exprs) => ppNary(exprs, "(", ", ", ")", lvl)
    case TupleSelect(t, i) =>
      pp(t, lvl)
      sb.append("._" + i)

    case CaseClass(cd, args) =>
      sb.append(cd.id)
      if (cd.isCaseObject) {
        ppNary(args, "", "", "", lvl)
      } else {
        ppNary(args, "(", ", ", ")", lvl)
      }

    case CaseClassInstanceOf(cd, e) =>
      pp(e, lvl)
      sb.append(".isInstanceOf[" + cd.id + "]")

    case CaseClassSelector(_, cc, id) =>
      pp(cc, lvl)
      sb.append("." + id)

    case FunctionInvocation(fd, args) =>
      sb.append(fd.id)
      ppNary(args, "(", ", ", ")", lvl)

    case Plus(l,r) => ppBinary(l, r, " + ", lvl)
    case Minus(l,r) => ppBinary(l, r, " - ", lvl)
    case Times(l,r) => ppBinary(l, r, " * ", lvl)
    case Division(l,r) => ppBinary(l, r, " / ", lvl)
    case Modulo(l,r) => ppBinary(l, r, " % ", lvl)
    case LessThan(l,r) => ppBinary(l, r, " < ", lvl)
    case GreaterThan(l,r) => ppBinary(l, r, " > ", lvl)
    case LessEquals(l,r) => ppBinary(l, r, " <= ", lvl)      // \leq
    case GreaterEquals(l,r) => ppBinary(l, r, " >= ", lvl)   // \geq
    case FiniteSet(rs) => ppNary(rs, "Set(", ", ", ")", lvl)
    case FiniteMultiset(rs) => ppNary(rs, "{|", ", ", "|}", lvl)
    case EmptyMultiset(_) => sys.error("Not Valid Scala")
    case ElementOfSet(e, s) => ppBinary(s, e, " contains ", lvl)
    //case ElementOfSet(s,e) => ppBinary(s, e, " \u2208 ", lvl)    // \in
    //case SubsetOf(l,r) => ppBinary(l, r, " \u2286 ", lvl)        // \subseteq
    //case Not(SubsetOf(l,r)) => ppBinary(l, r, " \u2288 ", lvl)        // \notsubseteq
    case SetMin(s) =>
      pp(s, lvl)
      sb.append(".min")
    case SetMax(s) =>
      pp(s, lvl)
      sb.append(".max")
    case SetUnion(l,r) => ppBinary(l, r, " ++ ", lvl)        // \cup
   // case MultisetUnion(l,r) => ppBinary(l, r, " \u222A ", lvl)   // \cup
   // case MapUnion(l,r) => ppBinary(l, r, " \u222A ", lvl)        // \cup
   case SetDifference(l,r) => ppBinary(l, r, " -- ", lvl)       
   // case MultisetDifference(l,r) => ppBinary(l, r, " \\ ", lvl)       
   case SetIntersection(l,r) => ppBinary(l, r, " & ", lvl) // \cap
   // case MultisetIntersection(l,r) => ppBinary(l, r, " \u2229 ", lvl) // \cap
    case SetCardinality(t) => ppUnary(t, "", ".size", lvl)
   // case MultisetCardinality(t) => ppUnary(t, "|", "|", lvl)
   // case MultisetPlus(l,r) => ppBinary(l, r, " \u228E ", lvl)    // U+
   // case MultisetToSet(e) => pp(e, lvl).append(".toSet")
    case FiniteMap(rs) =>
      sb.append("{")
      val sz = rs.size
      var c = 0
      rs.foreach{case (k, v) => {
        pp(k, lvl); sb.append(" -> "); pp(v, lvl); c += 1 ; if(c < sz) sb.append(", ")
      }}
      sb.append("}")

    case MapGet(m,k) =>
      pp(m, lvl)
      ppNary(Seq(k), "(", ",", ")", lvl)

    case MapIsDefinedAt(m,k) => {
      pp(m, lvl)
      sb.append(".isDefinedAt")
      ppNary(Seq(k), "(", ",", ")", lvl)
    }
    case ArrayLength(a) =>
      pp(a, lvl)
      sb.append(".length")

    case ArrayClone(a) =>
      pp(a, lvl)
      sb.append(".clone")

    case ArrayFill(size, v) =>
      sb.append("Array.fill(")
      pp(size, lvl)
      sb.append(")(")
      pp(v, lvl)
      sb.append(")")

    case ArrayMake(v) => sys.error("Not Scala Code")
    case ArraySelect(ar, i) =>
      pp(ar, lvl)
      sb.append("(")
      pp(i, lvl)
      sb.append(")")

    case ArrayUpdated(ar, i, v) =>
      pp(ar, lvl)
      sb.append(".updated(")
      pp(i, lvl)
      sb.append(", ")
      pp(v, lvl)
      sb.append(")")

    case FiniteArray(exprs) =>
      ppNary(exprs, "Array(", ", ", ")", lvl)

    case Distinct(exprs) =>
      sb.append("distinct")
      ppNary(exprs, "(", ", ", ")", lvl)
    
    case IfExpr(c, t, e) =>
      sb.append("if (")
      pp(c, lvl)
      sb.append(") {\n")
      ind(lvl+1)
      pp(t, lvl+1)
      sb.append("\n")
      ind(lvl)
      sb.append("} else {\n")
      ind(lvl+1)
      pp(e, lvl+1)
      sb.append("\n")
      ind(lvl)
      sb.append("}")

    case Choose(ids, pred) =>
      sb.append("(choose { (")
      for (((id, tpe), i) <- ids.map(id => (id, id.getType)).zipWithIndex) {
          sb.append(id.toString+": ")
          pp(tpe, lvl)
          if (i != ids.size-1) {
              sb.append(", ")
          }
      }
      sb.append(") =>\n")
      ind(lvl+1)
      pp(pred, lvl+1)
      sb.append("\n")
      ind(lvl)
      sb.append("})")

    case mex @ MatchExpr(s, csc) => {
      def ppc(p: Pattern): Unit = p match {
        //case InstanceOfPattern(None,     ctd) =>
        //case InstanceOfPattern(Some(id), ctd) =>
        case CaseClassPattern(bndr,     ccd, subps) => {
          bndr.foreach(b => sb.append(b + " @ "))
          sb.append(ccd.id).append("(")
          var c = 0
          val sz = subps.size
          subps.foreach(sp => {
            ppc(sp)
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
            ppc(p)
            sb.append(", ")
          })
          ppc(subPatterns.last)
          sb.append(")")
        }
        case _ => sb.append("Pattern?")
      }

      sb.append("(")
      pp(s, lvl)
      // if(mex.posInfo != "") {
      //   sb.append(" match@(" + mex.posInfo + ") {\n")
      // } else {
        sb.append(" match {\n")
      // }

      csc.foreach(cs => {
        ind(lvl+1)
        sb.append("case ")
        ppc(cs.pattern)
        cs.theGuard.foreach(g => {
          sb.append(" if ")
          pp(g, lvl+1)
        })
        sb.append(" =>\n")
        ind(lvl+2)
        pp(cs.rhs, lvl+2)
        sb.append("\n")
      })
      ind(lvl)
      sb.append("}")
      sb.append(")")
    }

    case ResultVariable() => sb.append("res")
    case Not(expr) => ppUnary(expr, "!(", ")", lvl)               // \neg

    case e @ Error(desc) => {
      sb.append("leon.Utils.error[")
      pp(e.getType, lvl)
      sb.append("](\"" + desc + "\")")
    }

    case (expr: PrettyPrintable) => expr.printWith(lvl, this)

    case _ => sb.append("Expr?")
  }

  // TYPE TREES
  // all type trees are printed in-line

  override def pp(tpe: TypeTree, lvl: Int): Unit = tpe match {
    case Untyped => sb.append("???")
    case UnitType => sb.append("Unit")
    case Int32Type => sb.append("Int")
    case BooleanType => sb.append("Boolean")
    case ArrayType(bt) =>
      sb.append("Array[")
      pp(bt, lvl)
      sb.append("]")
    case SetType(bt) =>
      sb.append("Set[")
      pp(bt, lvl)
      sb.append("]")
    case MapType(ft,tt) =>
      sb.append("Map[")
      pp(ft, lvl)
      sb.append(",")
      pp(tt, lvl)
      sb.append("]")
    case MultisetType(bt) =>
      sb.append("Multiset[")
      pp(bt, lvl)
      sb.append("]")
    case TupleType(tpes) => ppNaryType(tpes, "(", ", ", ")", lvl)
    case c: ClassType => sb.append(c.classDef.id)
    case _ => sb.append("Type?")
  }

  // DEFINITIONS
  // all definitions are printed with an end-of-line
  override def pp(defn: Definition, lvl: Int): Unit = {

    defn match {
      case Program(id, mainObj) => {
        assert(lvl == 0)
        pp(mainObj, lvl)
      }

      case ObjectDef(id, defs, invs) => {
        ind(lvl)
        sb.append("object ")
        sb.append(id)
        sb.append(" {\n")

        var c = 0
        val sz = defs.size

        defs.foreach(df => {
          pp(df, lvl+1)
          if(c < sz - 1) {
            sb.append("\n\n")
          }
          c = c + 1
        })

        sb.append("\n")
        ind(lvl)
        sb.append("}\n")
      }

      case AbstractClassDef(id, parent) =>
        ind(lvl)
        sb.append("sealed abstract class ")
        sb.append(id)
        parent.foreach(p => sb.append(" extends " + p.id))

      case CaseClassDef(id, parent, varDecls) =>
        ind(lvl)
        sb.append("case class ")
        sb.append(id)
        sb.append("(")
        var c = 0
        val sz = varDecls.size

        varDecls.foreach(vd => {
          sb.append(vd.id)
          sb.append(": ")
          pp(vd.tpe, lvl)
          if(c < sz - 1) {
            sb.append(", ")
          }
          c = c + 1
        })
        sb.append(")")
        parent.foreach(p => sb.append(" extends " + p.id))

      case fd @ FunDef(id, rt, args, body, pre, post) =>

        //for(a <- fd.annotations) {
        //  ind(lvl)
        //  sb.append("@" + a + "\n")
        //}

        ind(lvl)
        sb.append("def ")
        sb.append(id)
        sb.append("(")

        val sz = args.size
        var c = 0
        
        args.foreach(arg => {
          sb.append(arg.id)
          sb.append(" : ")
          pp(arg.tpe, lvl)

          if(c < sz - 1) {
            sb.append(", ")
          }
          c = c + 1
        })

        sb.append(") : ")
        pp(rt, lvl)
        sb.append(" = (")
        if(body.isDefined) {
          pre match {
            case None => pp(body.get, lvl)
            case Some(prec) => {
              sb.append("{\n")
              ind(lvl+1)
              sb.append("require(")
              pp(prec, lvl+1)
              sb.append(")\n")
              pp(body.get, lvl)
              sb.append("\n")
              ind(lvl)
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
            pp(res, lvl)
            sb.append(" => ") //TODO, not very general solution...
            pp(newPost, lvl)
            sb.append("))")
          }
        }

      case _ => sb.append("Defn?")
    }
  }
}

object ScalaPrinter {
  def apply(tree: Expr, indent: Int): String = {
    val printer = new ScalaPrinter()
    printer.pp(tree, indent)
    printer.toString
  }

  def apply(tree: Expr): String = {
    val printer = new ScalaPrinter()
    printer.pp(tree, 0)
    printer.toString
  }

  def apply(tpe: TypeTree): String = {
    val printer = new ScalaPrinter()
    printer.pp(tpe, 0)
    printer.toString
  }

  def apply(defn: Definition): String = {
    val printer = new ScalaPrinter()
    printer.pp(defn, 0)
    printer.toString
  }
}
