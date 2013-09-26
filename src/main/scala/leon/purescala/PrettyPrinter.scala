/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

import Common._
import Trees._
import TypeTrees._
import Definitions._

import java.lang.StringBuffer

/** This pretty-printer uses Unicode for some operators, to make sure we
 * distinguish PureScala from "real" Scala (and also because it's cute). */
class PrettyPrinter(sb: StringBuffer = new StringBuffer) {
  override def toString = sb.toString

  def append(str: String) {
    sb.append(str)
  }

  def ind(lvl: Int) {
    sb.append("  " * lvl)
  }

  // EXPRESSIONS
  // all expressions are printed in-line
  def ppUnary(expr: Expr, op1: String, op2: String, lvl: Int) {
    sb.append(op1)
    pp(expr, lvl)
    sb.append(op2)
  }

  def ppBinary(left: Expr, right: Expr, op: String, lvl: Int) {
    sb.append("(")
    pp(left, lvl)
    sb.append(op)
    pp(right, lvl)
    sb.append(")")
  }

  def ppNary(exprs: Seq[Expr], pre: String, op: String, post: String, lvl: Int) {
    sb.append(pre)
    val sz = exprs.size
    var c = 0

    exprs.foreach(ex => {
      pp(ex, lvl) ; c += 1 ; if(c < sz) sb.append(op)
    })

    sb.append(post)
  }

  def idToString(id: Identifier): String = id.toString

  def pp(tree: Expr, lvl: Int): Unit = tree match {
    case Variable(id) => sb.append(idToString(id))
    case DeBruijnIndex(idx) => sb.append("_" + idx)
    case LetTuple(bs,d,e) =>
      sb.append("(let (" + bs.map(idToString _).mkString(",") + " := ");
      pp(d, lvl)
      sb.append(") in\n")
      ind(lvl+1)
      pp(e, lvl+1)
      sb.append(")")

    case Let(b,d,e) =>
      sb.append("(let (" + idToString(b) + " := ");
      pp(d, lvl)
      sb.append(") in\n")
      ind(lvl+1)
      pp(e, lvl+1)
      sb.append(")")

    case LetDef(fd,body) =>
      sb.append("\n")
      pp(fd, lvl+1)
      sb.append("\n")
      sb.append("\n")
      ind(lvl)
      pp(body, lvl)

    case And(exprs) => ppNary(exprs, "(", " \u2227 ", ")", lvl)            // \land
    case Or(exprs) => ppNary(exprs, "(", " \u2228 ", ")", lvl)             // \lor
    case Not(Equals(l, r)) => ppBinary(l, r, " \u2260 ", lvl)    // \neq
    case Iff(l,r) => ppBinary(l, r, " <=> ", lvl)              
    case Implies(l,r) => ppBinary(l, r, " ==> ", lvl)              
    case UMinus(expr) => ppUnary(expr, "-(", ")", lvl)
    case Equals(l,r) => ppBinary(l, r, " == ", lvl)
    case IntLiteral(v) => sb.append(v)
    case BooleanLiteral(v) => sb.append(v)
    case StringLiteral(s) => sb.append("\"" + s + "\"")
    case UnitLiteral => sb.append("()")
    case t@Tuple(exprs) => ppNary(exprs, "(", ", ", ")", lvl)
    case s@TupleSelect(t, i) =>
      pp(t, lvl)
      sb.append("._" + i)

    case c@Choose(vars, pred) =>
      sb.append("choose("+vars.map(idToString _).mkString(", ")+" => ")
      pp(pred, lvl)
      sb.append(")")

    case CaseClass(cd, args) =>
      sb.append(idToString(cd.id))
      if (cd.isCaseObject) {
        ppNary(args, "", "", "", lvl)
      } else {
        ppNary(args, "(", ", ", ")", lvl)
      }

    case CaseClassInstanceOf(cd, e) =>
      pp(e, lvl)
      sb.append(".isInstanceOf[" + idToString(cd.id) + "]")

    case CaseClassSelector(_, cc, id) =>
      pp(cc, lvl)
      sb.append("." + idToString(id))

    case FunctionInvocation(fd, args) =>
      sb.append(idToString(fd.id))
      ppNary(args, "(", ", ", ")", lvl)

    case Plus(l,r) => ppBinary(l, r, " + ", lvl)
    case Minus(l,r) => ppBinary(l, r, " - ", lvl)
    case Times(l,r) => ppBinary(l, r, " * ", lvl)
    case Division(l,r) => ppBinary(l, r, " / ", lvl)
    case Modulo(l,r) => ppBinary(l, r, " % ", lvl)
    case LessThan(l,r) => ppBinary(l, r, " < ", lvl)
    case GreaterThan(l,r) => ppBinary(l, r, " > ", lvl)
    case LessEquals(l,r) => ppBinary(l, r, " \u2264 ", lvl)      // \leq
    case GreaterEquals(l,r) => ppBinary(l, r, " \u2265 ", lvl)   // \geq
    case FiniteSet(rs) => if(rs.isEmpty) sb.append("\u2205") /* Ø */ else ppNary(rs, "{", ", ", "}", lvl)
    case FiniteMultiset(rs) => ppNary(rs, "{|", ", ", "|}", lvl)
    case EmptyMultiset(_) => sb.append("\u2205")                     // Ø
    case Not(ElementOfSet(s,e)) => ppBinary(s, e, " \u2209 ", lvl) // \notin
    case ElementOfSet(s,e) => ppBinary(s, e, " \u2208 ", lvl)    // \in
    case SubsetOf(l,r) => ppBinary(l, r, " \u2286 ", lvl)        // \subseteq
    case Not(SubsetOf(l,r)) => ppBinary(l, r, " \u2288 ", lvl)        // \notsubseteq
    case SetMin(s) => pp(s, lvl); sb.append(".min")
    case SetMax(s) => pp(s, lvl); sb.append(".max")
    case SetUnion(l,r) => ppBinary(l, r, " \u222A ", lvl)        // \cup
    case MultisetUnion(l,r) => ppBinary(l, r, " \u222A ", lvl)   // \cup
    case MapUnion(l,r) => ppBinary(l, r, " \u222A ", lvl)        // \cup
    case SetDifference(l,r) => ppBinary(l, r, " \\ ", lvl)       
    case MultisetDifference(l,r) => ppBinary(l, r, " \\ ", lvl)       
    case SetIntersection(l,r) => ppBinary(l, r, " \u2229 ", lvl) // \cap
    case MultisetIntersection(l,r) => ppBinary(l, r, " \u2229 ", lvl) // \cap
    case SetCardinality(t) => ppUnary(t, "|", "|", lvl)
    case MultisetCardinality(t) => ppUnary(t, "|", "|", lvl)
    case MultisetPlus(l,r) => ppBinary(l, r, " \u228E ", lvl)    // U+
    case MultisetToSet(e) => pp(e, lvl); sb.append(".toSet")
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

    case MapIsDefinedAt(m,k) =>
      pp(m, lvl)
      sb.append(".isDefinedAt")
      ppNary(Seq(k), "(", ",", ")", lvl)
    
    case ArrayLength(a) =>
      pp(a, lvl)
      sb.append(".length")
    
    case ArrayClone(a) => 
      pp(a, lvl)
      sb.append(".clone")
    
    case fill@ArrayFill(size, v) => 
      sb.append("Array.fill(")
      pp(size, lvl)
      sb.append(")(")
      pp(v, lvl)
      sb.append(")")
    
    case am@ArrayMake(v) =>
      sb.append("Array.make(")
      pp(v, lvl)
      sb.append(")")    

    case sel@ArraySelect(ar, i) =>
      pp(ar, lvl)
      sb.append("(")
      pp(i, lvl)
      sb.append(")")

    case up@ArrayUpdated(ar, i, v) =>
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
      sb.append(")\n")
      ind(lvl+1)
      pp(t, lvl+1)
      sb.append("\n")
      ind(lvl)
      sb.append("else\n")
      ind(lvl+1)
      pp(e, lvl+1)

    case mex @ MatchExpr(s, csc) => {
      def ppc(p: Pattern): Unit = p match {
        //case InstanceOfPattern(None,     ctd) =>
        //case InstanceOfPattern(Some(id), ctd) =>
        case CaseClassPattern(bndr,     ccd, subps) => {
          bndr.foreach(b => sb.append(idToString(b) + " @ "))
          sb.append(idToString(ccd.id)).append("(")
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
        case WildcardPattern(Some(id)) => sb.append(idToString(id))
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
        sb.append(" => ")
        pp(cs.rhs, lvl+1)
        sb.append("\n")
      })
      ind(lvl)
      sb.append("}")
    }

    case Not(expr) => ppUnary(expr, "\u00AC(", ")", lvl)               // \neg

    case e @ Error(desc) =>
      sb.append("error(\"" + desc + "\")[")
      pp(e.getType, lvl)
      sb.append("]")

    case (expr: PrettyPrintable) => expr.printWith(lvl, this)

    case _ => sb.append("Expr?")
  }

  // TYPE TREES
  // all type trees are printed in-line
  def ppNaryType(tpes: Seq[TypeTree], pre: String, op: String, post: String, lvl: Int): Unit = {
    sb.append(pre)
    val sz = tpes.size
    var c = 0

    tpes.foreach(t => {
      pp(t, lvl) ; c += 1 ; if(c < sz) sb.append(op)
    })

    sb.append(post)
  }

  def pp(tpe: TypeTree, lvl: Int): Unit = tpe match {
    case Untyped => sb.append("???")
    case UnitType => sb.append("Unit")
    case Int32Type => sb.append("Int")
    case BooleanType => sb.append("Boolean")
    case ArrayType(bt) => sb.append("Array["); pp(bt, lvl); sb.append("]")
    case SetType(bt) => sb.append("Set["); pp(bt, lvl); sb.append("]")
    case MapType(ft,tt) =>  sb.append("Map["); pp(ft, lvl); sb.append(","); pp(tt, lvl); sb.append("]")
    case MultisetType(bt) => sb.append("Multiset["); pp(bt, lvl); sb.append("]")
    case TupleType(tpes) => ppNaryType(tpes, "(", ", ", ")", lvl)
    case c: ClassType => sb.append(c.classDef.id)
    case FunctionType(fts, tt) => {
      if (fts.size > 1)
        ppNaryType(fts, "(", ", ", ")", lvl)
      else if (fts.size == 1)
        pp(fts.head, lvl)
      sb.append(" => ")
      pp(tt, lvl)
    }
    case _ => sb.append("Type?")
  }

  // DEFINITIONS
  // all definitions are printed with an end-of-line
  def pp(defn: Definition, lvl: Int) {
    defn match {
      case Program(id, mainObj) => {
        assert(lvl == 0)
        sb.append("package ")
        sb.append(idToString(id))
        sb.append(" {\n")
        pp(mainObj, lvl+1)
        sb.append("}\n")
      }

      case ObjectDef(id, defs, invs) => {
        ind(lvl)
        sb.append("object ")
        sb.append(idToString(id))
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

      case AbstractClassDef(id, parent) => {
        ind(lvl)
        sb.append("sealed abstract class ")
        sb.append(idToString(id))
        parent.foreach(p => sb.append(" extends " + idToString(p.id)))
      }

      case CaseClassDef(id, parent, varDecls) => {
        ind(lvl)
        sb.append("case class ")
        sb.append(idToString(id))
        sb.append("(")
        var c = 0
        val sz = varDecls.size

        varDecls.foreach(vd => {
          sb.append(idToString(vd.id))
          sb.append(": ")
          pp(vd.tpe, lvl)
          if(c < sz - 1) {
            sb.append(", ")
          }
          c = c + 1
        })
        sb.append(")")
        parent.foreach(p => sb.append(" extends " + idToString(p.id)))
      }

      case fd: FunDef =>
        for(a <- fd.annotations) {
          ind(lvl)
          sb.append("@" + a + "\n")
        }

        fd.precondition.foreach(prec => {
          ind(lvl)
          sb.append("@pre : ")
          pp(prec, lvl)
          sb.append("\n")
        })

        fd.postcondition.foreach{ case (id, postc) => {
          ind(lvl)
          sb.append("@post: ")
          sb.append(idToString(id)+" => ")
          pp(postc, lvl)
          sb.append("\n")
        }}

        ind(lvl)
        sb.append("def ")
        sb.append(idToString(fd.id))
        sb.append("(")

        val sz = fd.args.size
        var c = 0
        
        fd.args.foreach(arg => {
          sb.append(arg.id)
          sb.append(" : ")
          pp(arg.tpe, lvl)

          if(c < sz - 1) {
            sb.append(", ")
          }
          c = c + 1
        })

        sb.append(") : ")
        pp(fd.returnType, lvl)
        sb.append(" = ")
        fd.body match {
          case Some(body) =>
            pp(body, lvl)

          case None =>
            sb.append("[unknown function implementation]")
        }

      case _ => sb.append("Defn?")
    }
  }
}

class EquivalencePrettyPrinter() extends PrettyPrinter() {
  override def idToString(id: Identifier) = id.name
}

object PrettyPrinter {
  def apply(tree: Expr): String = {
    val printer = new PrettyPrinter()
    printer.pp(tree, 0)
    printer.toString
  }

  def apply(tpe: TypeTree): String = {
    val printer = new PrettyPrinter()
    printer.pp(tpe, 0)
    printer.toString
  }

  def apply(defn: Definition): String = {
    val printer = new PrettyPrinter()
    printer.pp(defn, 0)
    printer.toString
  }
}

trait PrettyPrintable {
  def printWith(lvl: Int, printer: PrettyPrinter): Unit
}

