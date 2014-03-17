/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Common._
import Trees._
import TypeTrees._
import Definitions._

import utils._

import java.lang.StringBuffer
import PrinterHelpers._

case class PrinterContext(
  current: Tree,
  parent: Option[Tree],
  lvl: Int,
  printer: PrettyPrinter
)

object PrinterHelpers {
  implicit class Printable(val f: PrinterContext => Any) extends AnyVal {
    def print(ctx: PrinterContext) = f(ctx)
  }

  implicit class PrintingHelper(val sc: StringContext) extends AnyVal {

    def p(args: Any*)(implicit ctx: PrinterContext): Unit = {
      val printer = ctx.printer
      val sb      = printer.sb

      var strings     = sc.parts.iterator
      var expressions = args.iterator

      var extraInd = 0;
      var firstElem = true;

      while(strings.hasNext) {
        val s = strings.next.stripMargin

        // Compute indentation
        var start = s.lastIndexOf('\n')
        if(start >= 0 || firstElem) {
          var i = start+1;
          while(i < s.length && s(i) == ' ') {
            i += 1
          }
          extraInd = (i-start-1)/2
        }

        firstElem = false

        // Make sure new lines are also indented
        sb.append(s.replaceAll("\n", "\n"+("  "*ctx.lvl)))

        var nctx = ctx.copy(lvl = ctx.lvl + extraInd)

        if (expressions.hasNext) {
          val e = expressions.next

          e match {
            case (t1, t2) =>
              nary(Seq(t1, t2), " -> ").print(nctx)

            case ts: Seq[Any] =>
              nary(ts).print(nctx)

            case t: Tree =>
              nctx = nctx.copy(current = t, parent = Some(nctx.current))
              printer.pp(t)(nctx)

            case p: Printable =>
              p.print(nctx)

            case e =>
              sb.append(e.toString)
          }
        }
      }
    }
  }

  def nary(ls: Seq[Any], sep: String = ", "): Printable = {
    val strs = List("") ::: List.fill(ls.size-1)(sep)

    implicit pctx: PrinterContext =>
      new StringContext(strs: _*).p(ls: _*)
  }

  def typed(t: Tree with Typed): Printable = {
    implicit pctx: PrinterContext =>
      p"$t: ${t.getType}"
  }

  def typed(ts: Seq[Tree with Typed]): Printable = {
    nary(ts.map(typed))
  }
}

/** This pretty-printer uses Unicode for some operators, to make sure we
 * distinguish PureScala from "real" Scala (and also because it's cute). */
class PrettyPrinter(opts: PrinterOptions, val sb: StringBuffer = new StringBuffer) {

  override def toString = sb.toString

  protected def optP(body: => Any)(implicit ctx: PrinterContext) = {
    if (requiresParentheses(ctx.current, ctx.parent)) {
      sb.append("(")
      body
      sb.append(")")
    } else {
      body
    }
  }

  protected def optB(body: => Any)(implicit ctx: PrinterContext) = {
    if (requiresBraces(ctx.current, ctx.parent)) {
      sb.append("{")
      body
      sb.append("}")
    } else {
      body
    }
  }

  def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    
      case id: Identifier =>    
        val name = if (opts.printUniqueIds) {
          id.uniqueName
        } else {
          id.toString
        }
        val alphaNumDollar = "[\\w\\$]"
        // FIXME this does not account for class names with operator symbols
        def isLegalScalaId(id : String) = id.matches(
          s"${alphaNumDollar}+|[${alphaNumDollar}+_]?[!@#%^&*+-\\|~/?><:]+"
        )
        // Replace $opname with operator symbols
        val candidate = scala.reflect.NameTransformer.decode(name)
        
        if (isLegalScalaId(candidate)) p"$candidate" else p"$name"
        
      case Variable(id) =>
        p"$id"

      case LetTuple(bs,d,e) =>
        e match {
          case _:LetDef | _ : Let | _ : LetTuple =>
            p"""|val ($bs) = {
                |  $d
                |}
                |$e"""
          case _ =>
            p"""|val ($bs) = $d;
                |$e"""
        }
      case Let(b,d,e) =>
        e match {
          case _:LetDef | _ : Let | _ : LetTuple =>
            p"""|val $b = {
                |  $d
                |}
                |$e"""
          case _ =>
            p"""|val $b = $d;
                |$e"""
        }
      case LetDef(fd,body) =>
        p"""|$fd
            |$body"""

      case Require(pre, body) =>
        p"""|require($pre)
            |$body"""

      case Assert(const, Some(err), body) =>
        p"""|assert($const, "$err")
            |$body"""

      case Assert(const, None, body) =>
        p"""|assert($const)
            |$body"""

      case Ensuring(body, id, post) =>
        p"""|{
            |  $body
            |} ensuring {
            |  (${typed(id)}) => $post
            |}"""

      case c @ WithOracle(vars, pred) =>
        p"""|withOracle { (${typed(vars)}) =>
            |  $pred
            |}"""

      case h @ Hole(tpe, es) =>
        if (es.isEmpty) {
          p"""|???[$tpe]"""
        } else {
          p"""|?($es)"""
        }

      case CaseClass(cct, args) =>
        if (cct.classDef.isCaseObject) {
          p"$cct"
        } else {
          p"$cct($args)"
        }

      case And(exprs)           => optP { p"${nary(exprs, " && ")}" }
      case Or(exprs)            => optP { p"${nary(exprs, "| || ")}" }
      case Not(Equals(l, r))    => optP { p"$l \u2260 $r" }
      case Iff(l,r)             => optP { p"$l <=> $r" }
      case Implies(l,r)         => optP { p"$l ==> $r" }
      case UMinus(expr)         => p"-$expr"
      case Equals(l,r)          => optP { p"$l == $r" }
      case IntLiteral(v)        => p"$v"
      case BooleanLiteral(v)    => p"$v"
      case StringLiteral(s)     => p""""$s""""
      case UnitLiteral()        => p"()"
      case GenericValue(tp, id) => p"$tp#$id"
      case Tuple(exprs)         => p"($exprs)"
      case TupleSelect(t, i)    => p"${t}._$i"
      case Choose(vars, pred)   => p"choose(($vars) => $pred)"
      case e @ Error(err)       => p"""error[${e.getType}]("$err")"""
      case CaseClassInstanceOf(cct, e)         =>
        if (cct.classDef.isCaseObject) {
          p"($e == ${cct.id})"
        } else {
          p"$e.isInstanceOf[$cct]"
        }
      case CaseClassSelector(_, e, id)         => p"$e.$id"
      case MethodInvocation(rec, _, tfd, args) =>
        p"$rec.${tfd.id}"

        if (tfd.tps.nonEmpty) {
          p"[${tfd.tps}]"
        }

        p"($args)"

      case FunctionInvocation(tfd, args) =>
        p"${tfd.id}"

        if (tfd.tps.nonEmpty) {
          p"[${tfd.tps}]"
        }

        p"($args)"

      case Plus(l,r)                 => optP { p"$l + $r" }
      case Minus(l,r)                => optP { p"$l - $r" }
      case Times(l,r)                => optP { p"$l * $r" }
      case Division(l,r)             => optP { p"$l / $r" }
      case Modulo(l,r)               => optP { p"$l % $r" }
      case LessThan(l,r)             => optP { p"$l < $r" }
      case GreaterThan(l,r)          => optP { p"$l > $r" }
      case LessEquals(l,r)           => optP { p"$l <= $r" }
      case GreaterEquals(l,r)        => optP { p"$l >= $r" }
      case FiniteSet(rs)             => p"{$rs}"
      case FiniteMultiset(rs)        => p"{|$rs|)"
      case EmptyMultiset(_)          => p"\u2205"
      case Not(ElementOfSet(e,s))    => p"$e \u2209 $s"
      case ElementOfSet(e,s)         => p"$e \u2208 $s"
      case SubsetOf(l,r)             => p"$l \u2286 $r"
      case Not(SubsetOf(l,r))        => p"$l \u2288 $r"
      case SetMin(s)                 => p"$s.min"
      case SetMax(s)                 => p"$s.max"
      case SetUnion(l,r)             => p"$l \u222A $r"
      case MultisetUnion(l,r)        => p"$l \u222A $r"
      case MapUnion(l,r)             => p"$l \u222A $r"
      case SetDifference(l,r)        => p"$l \\ $r"
      case MultisetDifference(l,r)   => p"$l \\ $r"
      case SetIntersection(l,r)      => p"$l \u2229 $r"
      case MultisetIntersection(l,r) => p"$l \u2229 $r"
      case SetCardinality(s)         => p"|$s|"
      case MultisetCardinality(s)    => p"|$s|"
      case MultisetPlus(l,r)         => p"$l \u228E $r"
      case MultisetToSet(e)          => p"$e.toSet"
      case MapGet(m,k)               => p"$m($k)"
      case MapIsDefinedAt(m,k)       => p"$m.isDefinedAt($k)"
      case ArrayLength(a)            => p"$a.length"
      case ArrayClone(a)             => p"$a.clone"
      case ArrayFill(size, v)        => p"Array.fill($size)($v)"
      case ArrayMake(v)              => p"Array.make($v)"
      case ArraySelect(a, i)         => p"$a($i)"
      case ArrayUpdated(a, i, v)     => p"$a.updated($i, $v)"
      case FiniteArray(exprs)        => p"Array($exprs)"
      case Distinct(exprs)           => p"distinct($exprs)"
      case Not(expr)                 => p"\u00AC$expr"
      case ValDef(id, tpe)           => p"${typed(id)}"
      case This(_)                   => p"this"
      case (tfd: TypedFunDef)        => p"typed def ${tfd.id}[${tfd.tps}]"
      case TypeParameterDef(tp)      => p"$tp"
      case TypeParameter(id)         => p"$id"

      case FiniteMap(rs) =>
        p"{$rs}"


      case IfExpr(c, t, e) =>
        optP {
          p"""|if ($c) {
              |  $t
              |} else {
              |  $e
              |}"""
        }

      case MatchExpr(s, csc) =>
        optP {
          p"""|$s match {
              |  ${nary(csc, "\n")}
              |}"""
        }

      // Cases
      case SimpleCase(pat, rhs) =>
        p"""|case $pat =>
            |  $rhs"""

      case GuardedCase(pat, guard, rhs) =>
        p"""|case $pat if $guard =>
            |  $rhs"""

      // Patterns
      case WildcardPattern(None)     => p"_"
      case WildcardPattern(Some(id)) => p"$id"

      case CaseClassPattern(ob, cct, subps) =>
        ob.foreach { b => p"$b @ " }
        if (cct.classDef.isCaseObject) {
          p"${cct.id}"
        } else {
          p"${cct.id}($subps)"
        }

      case InstanceOfPattern(ob, cct) =>
        if (cct.classDef.isCaseObject) {
          ob.foreach { b => p"$b @ " }
          p"${cct.id}"
        } else {
          ob.foreach { b => p"$b : " }
          p"$cct"
        }

      case TuplePattern(ob, subps) =>
        ob.foreach { b => p"$b @ " }
        p"($subps)"

      // Types
      case Untyped               => p"<untyped>"
      case UnitType              => p"Unit"
      case Int32Type             => p"Int"
      case BooleanType           => p"Boolean"
      case ArrayType(bt)         => p"Array[$bt]"
      case SetType(bt)           => p"Set[$bt]"
      case MapType(ft,tt)        => p"Map[$ft, $tt]"
      case MultisetType(bt)      => p"Multiset[$bt]"
      case TupleType(tpes)       => p"($tpes)"
      case FunctionType(fts, tt) => p"($fts) => $tt"
      case c: ClassType =>
        p"${c.classDef.id}"
        if (c.tps.nonEmpty) {
          p"[${c.tps}]"
        }


      // Definitions
      case Program(id, modules) =>
        p"""|package $id {
            |  ${nary(modules, "\n\n")}
            |}"""

      case ModuleDef(id, defs) =>
        p"""|object $id {
            |  ${nary(defs, "\n\n")}
            |}"""

      case acd @ AbstractClassDef(id, tparams, parent) =>
        p"abstract class $id"

        if (tparams.nonEmpty) {
          p"[$tparams]"
        }

        parent.foreach{ par =>
          p" extends ${par.id}"
        }

        if (acd.methods.nonEmpty) {
          p"""| {
              |  ${nary(acd.methods, "\n\n")}
              |}"""
        }

      case ccd @ CaseClassDef(id, tparams, parent, isObj) =>
        if (isObj) {
          p"case object $id"
        } else {
          p"case class $id"
        }

        if (tparams.nonEmpty) {
          p"[$tparams]"
        }

        if (!isObj) {
          p"(${ccd.fields})"
        }

        parent.foreach{ par =>
          if (par.tps.nonEmpty){
            p" extends ${par.id}[${par.tps}]"
          } else {
            p" extends ${par.id}"
          }
        }

        if (ccd.methods.nonEmpty) {
          p"""| {
              |  ${nary(ccd.methods, "\n\n")}
              |}"""
        }

      case fd: FunDef =>
        for(a <- fd.annotations) {
          p"""|@$a
              |"""
        }


        p"""|def ${fd.id}(${fd.params}): ${fd.returnType} = {
            |"""

        fd.precondition.foreach { case pre =>
          p"""|  require($pre)
              |"""
        }

        fd.body match {
          case Some(b) =>
            p"  $b"

          case None =>
            p"???"
        }

        p"""|
            |}"""

        fd.postcondition.foreach { case (id, post) =>
          p"""| ensuring {
              |  (${typed(id)}) => $post
              |}"""
        }

      case (tree: PrettyPrintable) => tree.printWith(ctx)

      case _ => sb.append("Tree? (" + tree.getClass + ")")
    
  }

  def requiresBraces(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (pa: PrettyPrintable, _) => pa.printRequiresBraces(within)
    case (_, None) => false
    case (_: Require, Some(_: Ensuring)) => false
    case (_: Require, _) => true
    case (_: Assert, Some(_: Definition)) => true
    case (_, Some(_: Definition)) => false
    case (_, Some(_: MatchExpr | _: MatchCase | _: Let | _: LetTuple | _: LetDef)) => false
    case (_, _) => true
  }

  def precedence(ex: Expr): Int = ex match {
    case (pa: PrettyPrintable) => pa.printPrecedence
    case (_: ElementOfSet) => 0
    case (_: Or) => 1
    case (_: And) => 3
    case (_: GreaterThan | _: GreaterEquals  | _: LessEquals | _: LessThan) => 4
    case (_: Equals | _: Iff | _: Not) => 5
    case (_: Plus | _: Minus | _: SetUnion| _: SetDifference) => 6
    case (_: Times | _: Division | _: Modulo) => 7
    case _ => 7
  }

  def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (pa: PrettyPrintable, _) => pa.printRequiresParentheses(within)
    case (_, None) => false
    case (_, Some(_: Ensuring)) => false
    case (_, Some(_: Assert)) => false
    case (_, Some(_: Require)) => false
    case (_, Some(_: Definition)) => false
    case (_, Some(_: MatchExpr | _: MatchCase | _: Let | _: LetTuple | _: LetDef | _: IfExpr)) => false
    case (_, Some(_: FunctionInvocation)) => false
    case (ie: IfExpr, _) => true
    case (me: MatchExpr, _ ) => true
    case (e1: Expr, Some(e2: Expr)) if precedence(e1) > precedence(e2) => false
    case (_, _) => true
  }
}

trait PrettyPrintable {
  self: Tree =>

  def printWith(implicit pctx: PrinterContext): Unit

  def printPrecedence: Int = 1000
  def printRequiresParentheses(within: Option[Tree]): Boolean = false
  def printRequiresBraces(within: Option[Tree]): Boolean = false
}

class EquivalencePrettyPrinter(opts: PrinterOptions) extends PrettyPrinter(opts) {
  override def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {
    tree match {
      case id: Identifier =>
        p"""${id.name}"""

      case _ =>
        super.pp(tree)
    }
  }
}

abstract class PrettyPrinterFactory {
  def create(opts: PrinterOptions): PrettyPrinter

  def apply(tree: Tree, opts: PrinterOptions = PrinterOptions()): String = {
    val printer = create(opts)
    val ctx = PrinterContext(tree, None, opts.baseIndent, printer)
    printer.pp(tree)(ctx)
    printer.toString
  }

  def apply(tree: Tree, ctx: LeonContext): String = {
    val opts = PrinterOptions.fromContext(ctx)
    apply(tree, opts)
  }
}

object PrettyPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions) = new PrettyPrinter(opts)
}

object EquivalencePrettyPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions) = new EquivalencePrettyPrinter(opts)
}
