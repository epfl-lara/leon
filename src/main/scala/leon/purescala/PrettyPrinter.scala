/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import leon.utils._
import Common._
import DefOps._
import Definitions._
import Extractors._
import PrinterHelpers._
import ExprOps.{ isListLiteral, simplestValue }
import Expressions._
import Constructors._
import Types._
import org.apache.commons.lang3.StringEscapeUtils

case class PrinterContext(
    current: Tree,
    parents: List[Tree],
    lvl: Int,
    printer: PrettyPrinter) {

  def parent = parents.headOption
}

/**
 * This pretty-printer uses Unicode for some operators, to make sure we
 * distinguish PureScala from "real" Scala (and also because it's cute).
 */
class PrettyPrinter(opts: PrinterOptions,
                    opgm: Option[Program],
                    val sb: StringBuffer = new StringBuffer) {

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

  protected def getScope(implicit ctx: PrinterContext) =
    ctx.parents.collectFirst { case (d: Definition) if !d.isInstanceOf[ValDef] => d }

  protected def printNameWithPath(df: Definition)(implicit ctx: PrinterContext) {
    (opgm, getScope) match {
      case (Some(pgm), Some(scope)) =>
        sb.append(fullNameFrom(df, scope, opts.printUniqueIds)(pgm))

      case _ =>
        p"${df.id}"
    }
  }

  private val dbquote = "\""

  def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {

    if (requiresBraces(tree, ctx.parent) && !ctx.parent.contains(tree)) {
      p"""|{
          |  $tree
          |}"""
      return
    }

    if (opts.printTypes) {
      tree match {
        case t: Expr =>
          p"⟨"

        case _ =>
      }
    }
    tree match {
      case id: Identifier =>
        val name = if (opts.printUniqueIds) {
          id.uniqueName
        } else {
          id.toString
        }
        p"$name"

      case Variable(id) =>
        p"$id"

      case Let(id, expr, SubString(Variable(id2), start, StringLength(Variable(id3)))) if id == id2 && id2 == id3 =>
        p"$expr.substring($start)"

      case Let(id, expr, BigSubString(Variable(id2), start, StringLength(Variable(id3)))) if id == id2 && id2 == id3 =>
        p"$expr.bigSubstring($start)"

      case Let(b, d, e) =>
        p"""|val $b: ${b.getType} = $d
            |$e"""

      case LetDef(a +: q, body) =>
        p"""|$a
            |${letDef(q, body)}"""
      case LetDef(Nil, body) =>
        p"""$body"""

      case Require(BooleanLiteral(true), body) =>
        p"|$body"

      case Require(pre, body) =>
        p"""|require($pre)
            |$body"""

      case Assert(const, Some(err), body) =>
        p"""|assert($const, "$err")
            |$body"""

      case Assert(const, None, body) =>
        p"""|assert($const)
            |$body"""

      case Ensuring(body, post) =>
        p"""| {
            |  $body
            |} ensuring {
            |  $post
            |}"""

      case p @ Passes(in, out, tests) =>
        tests match {
          case Seq(MatchCase(_, Some(BooleanLiteral(false)), NoTree(_))) =>
            p"""|byExample($in, $out)"""
          case _ =>
            optP {
              p"""|($in, $out) passes {
                  |  ${nary(tests, "\n")}
                  |}"""
            }
        }

      case c @ WithOracle(vars, pred) =>
        p"""|withOracle { (${typed(vars)}) =>
            |  $pred
            |}"""

      case h @ Hole(tpe, es) =>
        if (es.isEmpty) {
          val hole = (for {
            scope <- getScope
            program <- opgm
          } yield simplifyPath("leon" :: "lang" :: "synthesis" :: "???" :: Nil, scope, false)(program))
            .getOrElse("leon.lang.synthesis.???")
          p"$hole[$tpe]"
        } else {
          p"?($es)"
        }

      case Forall(args, e) =>
        p"\u2200${typed(args.map(_.id))}. $e"

      case e @ CaseClass(cct, args) =>
        opgm.flatMap { pgm => isListLiteral(e)(pgm) } match {
          case Some((tpe, elems)) =>
            if(elems.length > 0 && elems.forall { x => x.getType == tpe }) {
              printNameWithPath(opgm.get.library.List.get)
              p"($elems)"
            } else {
              val lclass = AbstractClassType(opgm.get.library.List.get, cct.tps)
              p"$lclass($elems)"
            }

          case None =>
            if (cct.classDef.isCaseObject) {
              p"$cct"
            } else {
              p"$cct($args)"
            }
        }

      case And(exprs)                     => optP { p"${nary(exprs, " && ")}" }
      case Or(exprs)                      => optP { p"${nary(exprs, "| || ")}" } // Ugliness award! The first | is there to shield from stripMargin()
      case Not(Equals(l, r))              => optP { p"$l \u2260 $r" }
      case Implies(l, r)                  => optP { p"$l ==> $r" }
      case BVNot(expr)                    => p"~$expr"
      case UMinus(expr)                   => p"-$expr"
      case BVUMinus(expr)                 => p"-$expr"
      case RealUMinus(expr)               => p"-$expr"
      case Equals(l, r)                   => optP { p"$l == $r" }

      case Int32ToString(expr)            => p"$expr.toString"
      case BooleanToString(expr)          => p"$expr.toString"
      case IntegerToString(expr)          => p"$expr.toString"
      case CharToString(expr)             => p"$expr.toString"
      case RealToString(expr)             => p"$expr.toString"
      case StringConcat(lhs, rhs)         => optP { p"$lhs + $rhs" }

      case SubString(expr, start, end)    => p"$expr.substring($start, $end)"
      case BigSubString(expr, start, end) => p"$expr.bigSubstring($start, $end)"
      case StringLength(expr)             => p"$expr.length"
      case StringBigLength(expr)          => p"$expr.bigLength"

      case ByteLiteral(v)                 => p"$v"
      case IntLiteral(v)                  => p"$v"
      case InfiniteIntegerLiteral(v)      => p"$v"
      case FractionalLiteral(n, d) =>
        if (d == 1) p"$n"
        else p"$n/$d"
      case CharLiteral(v)    => p"$v"
      case BooleanLiteral(v) => p"$v"
      case UnitLiteral()     => p"()"
      case StringLiteral(v) =>
        val newlineCount = v.count(c => c == '\n')
        if (newlineCount >= 1 && (v.length >= 80 || (newlineCount >= 3 && newlineCount < v.length / 3)) && v.indexOf("\"\"\"") == -1) {
          p"$dbquote$dbquote$dbquote$v$dbquote$dbquote$dbquote"
        } else {
          val escaped = StringEscapeUtils.escapeJava(v)
          p"$dbquote$escaped$dbquote"
        }

      case ArrayForall(a, IntLiteral(0), ArrayLength(a2), pred) if a == a2 =>
        p"$a.forall($pred)"
      case ArrayForall(a, from, to, pred) =>
        p"$a.forall($from, $to, $pred)"
      case BoundedForall(from, to, pred) =>
        p"forall($from, $to, $pred)"

      case ArrayExists(a, IntLiteral(0), ArrayLength(a2), pred) if a == a2 =>
        p"$a.exists($pred)"
      case ArrayExists(a, from, to, pred) =>
        p"$a.exists($from, $to, $pred)"
      case BoundedExists(from, to, pred) =>
        p"exists($from, $to, $pred)"

      case GenericValue(tp, id) => p"$tp#$id"
      case Tuple(exprs)         => p"($exprs)"
      case TupleSelect(t, i)    => p"$t._$i"
      case NoTree(tpe)          => p"<empty tree>[$tpe]"
      case Choose(pred) =>
        val choose = (for {
          scope <- getScope
          program <- opgm
        } yield simplifyPath("leon" :: "lang" :: "synthesis" :: "choose" :: Nil, scope, false)(program))
          .getOrElse("leon.lang.synthesis.choose")
        p"$choose($pred)"
      case e @ Error(tpe, err) => p"""error[$tpe]("$err")"""
      case AsInstanceOf(e, ct) => p"""$e.asInstanceOf[$ct]"""
      case IsInstanceOf(e, cct) =>
        if (cct.classDef.isCaseObject) {
          p"($e == $cct)"
        } else {
          p"$e.isInstanceOf[$cct]"
        }
      case CaseClassSelector(_, e, id) => p"$e.$id"
      case MethodInvocation(rec, _, tfd, args) =>
        p"$rec.${tfd.id}${nary(tfd.tps, ", ", "[", "]")}"
        // No () for fields
        if (tfd.fd.isRealFunction) {
          // The non-present arguments are synthetic function invocations
          val presentArgs = args filter {
            case MethodInvocation(_, _, tfd, _) if tfd.fd.isSynthetic => false
            case FunctionInvocation(tfd, _) if tfd.fd.isSynthetic => false
            case other => true
          }

          val requireParens = presentArgs.nonEmpty || args.nonEmpty
          if (requireParens) {
            p"($presentArgs)"
          }
        }

      case BinaryMethodCall(a, op, b) =>
        optP { p"$a $op $b" }

      case FcallMethodInvocation(rec, fd, id, tps, args) if (fd.annotations.contains("library") || !(opts.printRunnableCode)) =>

        p"$rec.$id${nary(tps, ", ", "[", "]")}"

        if (fd.isRealFunction) {
          // The non-present arguments are synthetic function invocations
          val presentArgs = args filter {
            case MethodInvocation(_, _, tfd, _) if tfd.fd.isSynthetic => false
            case FunctionInvocation(tfd, _) if tfd.fd.isSynthetic => false
            case other => true
          }

          val requireParens = presentArgs.nonEmpty || args.nonEmpty
          if (requireParens) {
            p"($presentArgs)"
          }
        }

      case FunctionInvocation(TypedFunDef(fd, tps), args) =>
        printNameWithPath(fd)

        p"${nary(tps, ", ", "[", "]")}"

        if (fd.isRealFunction) {
          // The non-present arguments are synthetic function invocations
          val presentArgs = args filter {
            case MethodInvocation(_, _, tfd, _) if tfd.fd.isSynthetic => false
            case FunctionInvocation(tfd, _) if tfd.fd.isSynthetic => false
            case other => true
          }
          val requireParens = presentArgs.nonEmpty || args.nonEmpty
          if (requireParens) {
            p"($presentArgs)"
          }
        }

      case Application(caller, args) =>
        p"$caller($args)"

      case Lambda(Seq(ValDef(id)), FunctionInvocation(TypedFunDef(fd, Seq()), Seq(Variable(idArg)))) if id == idArg =>
        printNameWithPath(fd)

      case Lambda(args, body) =>
        optP { p"($args) => $body" }

      case FiniteLambda(mapping, dflt, _) =>
        optP {
          def pm(p: (Seq[Expr], Expr)): PrinterHelpers.Printable =
            (pctx: PrinterContext) => p"${purescala.Constructors.tupleWrap(p._1)} => ${p._2}"(pctx)

          if (mapping.isEmpty) {
            p"{ * => ${dflt} }"
          } else {
            p"{ ${nary(mapping map pm)}, * => ${dflt} }"
          }
        }

      case Plus(l, r)               => optP { p"$l + $r" }
      case Minus(l, r)              => optP { p"$l - $r" }
      case Times(l, r)              => optP { p"$l * $r" }
      case Division(l, r)           => optP { p"$l / $r" }
      case Remainder(l, r)          => optP { p"$l % $r" }
      case Modulo(l, r)             => optP { p"$l mod $r" }
      case LessThan(l, r)           => optP { p"$l < $r" }
      case GreaterThan(l, r)        => optP { p"$l > $r" }
      case LessEquals(l, r)         => optP { p"$l <= $r" }
      case GreaterEquals(l, r)      => optP { p"$l >= $r" }
      case BVPlus(l, r)             => optP { p"$l + $r" }
      case BVMinus(l, r)            => optP { p"$l - $r" }
      case BVTimes(l, r)            => optP { p"$l * $r" }
      case BVDivision(l, r)         => optP { p"$l / $r" }
      case BVRemainder(l, r)        => optP { p"$l % $r" }
      case BVAnd(l, r)              => optP { p"$l & $r" }
      case BVOr(l, r)               => optP { p"$l | $r" }
      case BVXOr(l, r)              => optP { p"$l ^ $r" }
      case BVShiftLeft(l, r)        => optP { p"$l << $r" }
      case BVAShiftRight(l, r)      => optP { p"$l >> $r" }
      case BVLShiftRight(l, r)      => optP { p"$l >>> $r" }
      case BVNarrowingCast(e, Int32Type) => p"$e.toInt"
      case BVNarrowingCast(e, Int8Type)  => p"$e.toByte"
      case BVWideningCast(e, Int32Type)  => p"$e.toInt"
      case BVWideningCast(e, Int8Type)   => p"$e.toByte"
      case RealPlus(l, r)           => optP { p"$l + $r" }
      case RealMinus(l, r)          => optP { p"$l - $r" }
      case RealTimes(l, r)          => optP { p"$l * $r" }
      case RealDivision(l, r)       => optP { p"$l / $r" }
      case fs @ FiniteSet(rs, _)    => p"{${rs.toSeq}}"
      case fs @ FiniteBag(rs, _)    => p"{$rs}"
      case fm @ FiniteMap(rs, _, _) => p"{${rs.toSeq}}"
      case Not(ElementOfSet(e, s))  => p"$e \u2209 $s"
      case ElementOfSet(e, s)       => p"$e \u2208 $s"
      case SubsetOf(l, r)           => p"$l \u2286 $r"
      case Not(SubsetOf(l, r))      => p"$l \u2288 $r"
      case SetAdd(s, e)             => p"$s \u222A {$e}"
      case SetUnion(l, r)           => p"$l \u222A $r"
      case BagUnion(l, r)           => p"$l \u222A $r"
      case MapUnion(l, r)           => p"$l \u222A $r"
      case SetDifference(l, r)      => p"$l \\ $r"
      case BagDifference(l, r)      => p"$l \\ $r"
      case SetIntersection(l, r)    => p"$l \u2229 $r"
      case BagIntersection(l, r)    => p"$l \u2229 $r"
      case SetCardinality(s)        => p"$s.size"
      case BagAdd(b, e)             => p"$b + $e"
      case MultiplicityInBag(e, b)  => p"$b($e)"
      case MapApply(m, k)           => p"$m($k)"
      case MapIsDefinedAt(m, k)     => p"$m.isDefinedAt($k)"
      case ArrayLength(a)           => p"$a.length"
      case ArraySelect(a, i)        => p"$a($i)"
      case ArrayUpdated(a, i, v)    => p"$a.updated($i, $v)"
      case a @ FiniteArray(es, d, s) => {
        def ppBigArray(): Unit = {
          if (es.isEmpty) {
            val simplest = a.getType match {
              case ArrayType(underlying) => simplestValue(underlying)
              case _ => NoTree
            }
            val default = d.getOrElse(simplest)
            p"Array($default, $default, $default, ..., $default) (of size $s)"
          } else {
            p"Array(_) (of size $s)"
          }
        }
        s match {
          case IntLiteral(length) => {
            if (es.size == length) {
              val orderedElements = es.toSeq.sortWith((e1, e2) => e1._1 < e2._1).map(el => el._2)
              p"Array($orderedElements)"
            } else if (length < 10) {
              val elems = (0 until length).map(i =>
                es.find(el => el._1 == i).map(el => el._2).getOrElse(d.get))
              p"Array($elems)"
            } else {
              ppBigArray()
            }
          }
          case _ => ppBigArray()
        }
      }

      case Not(expr) => p"\u00AC$expr"

      case vd @ ValDef(id) =>
        if (vd.isVar)
          p"var "
        p"$id : ${vd.getType}"
        vd.defaultValue.foreach { fd => p" = ${fd.body.get}" }

      case This(_)              => p"this"
      case (tfd: TypedFunDef)   => p"typed def ${tfd.id}[${tfd.tps}]"
      case TypeParameterDef(tp) => p"$tp"
      case TypeParameter(id)    => p"$id"

      case IfExpr(c, t, ie: IfExpr) =>
        optP {
          p"""|if ($c) {
              |  $t
              |} else $ie"""
        }

      case IfExpr(c, t, e) =>
        optP {
          p"""|if ($c) {
              |  $t
              |} else {
              |  $e
              |}"""
        }

      case LetPattern(p, s, rhs) =>
        p"""|val $p = $s
            |$rhs"""

      case MatchExpr(s, csc) =>
        optP {
          p"""|$s match {
              |  ${nary(csc, "\n")}
              |}"""
        }

      // Cases
      case MatchCase(pat, optG, rhs) =>
        p"|case $pat "; optG foreach { g => p"if $g " }; p"""=>
          |  $rhs"""

      // Patterns
      case WildcardPattern(None)     => p"_"
      case WildcardPattern(Some(id)) => p"$id"

      case CaseClassPattern(ob, cct, subps) =>
        ob.foreach { b => p"$b @ " }
        // Print only the classDef because we don't want type parameters in patterns
        printNameWithPath(cct.classDef)
        if (!cct.classDef.isCaseObject) p"($subps)"

      case InstanceOfPattern(ob, cct) =>
        if (cct.classDef.isCaseObject) {
          ob.foreach { b => p"$b @ " }
        } else {
          ob.foreach { b => p"$b : " }
        }
        // It's ok to print the whole type because there are no type parameters for case objects
        p"$cct"

      case TuplePattern(ob, subps) =>
        ob.foreach { b => p"$b @ " }
        p"($subps)"

      case UnapplyPattern(ob, tfd, subps) =>
        ob.foreach { b => p"$b @ " }

        // @mk: I admit this is pretty ugly
        (for {
          p <- opgm
          mod <- p.modules.find(_.definedFunctions contains tfd.fd)
        } yield mod) match {
          case Some(obj) =>
            printNameWithPath(obj)
          case None =>
            p"<unknown object>"
        }

        p"(${nary(subps)})"

      case LiteralPattern(ob, lit) =>
        ob foreach { b => p"$b @ " }
        p"$lit"

      // Types
      case Untyped               => p"<untyped>"
      case UnitType              => p"Unit"
      case Int8Type              => p"Byte"
      case Int32Type             => p"Int"
      case IntegerType           => p"BigInt"
      case RealType              => p"Real"
      case CharType              => p"Char"
      case BooleanType           => p"Boolean"
      case StringType            => p"String"
      case ArrayType(bt)         => p"Array[$bt]"
      case SetType(bt)           => p"Set[$bt]"
      case BagType(bt)           => p"Bag[$bt]"
      case MapType(ft, tt)       => p"Map[$ft, $tt]"
      case TupleType(tpes)       => p"($tpes)"
      case FunctionType(fts, tt) => p"($fts) => $tt"
      case c: ClassType =>
        printNameWithPath(c.classDef)
        p"${nary(c.tps, ", ", "[", "]")}"

      // Definitions
      case Program(units) =>
        p"""${nary(units filter { /*opts.printUniqueIds ||*/ _.isMainUnit }, "\n\n")}"""

      case UnitDef(id, pack, imports, defs, _) =>
        if (pack.nonEmpty && (!(opts.printRunnableCode))) {
          p"""|package ${pack mkString "."}
              |"""
        }
        p"""|${nary(imports, "\n")}
            |
            |${nary(defs, "\n\n")}
            |"""

      case Import(path, isWild) =>
        if (isWild) {
          p"import ${nary(path, ".")}._"
        } else {
          p"import ${nary(path, ".")}"
        }

      case ModuleDef(id, defs, _) =>
        p"""|object $id {
            |  ${nary(defs, "\n\n")}
            |}"""

      case acd: AbstractClassDef =>
        p"abstract class ${acd.id}${nary(acd.tparams, ", ", "[", "]")}"

        acd.parent.foreach { par =>
          p" extends ${par.id}"
        }

        if (acd.methods.nonEmpty) {
          p"""| {
              |  ${nary(acd.methods, "\n\n")}
              |}"""
        }

      case ccd: CaseClassDef =>
        if (ccd.isCaseObject) {
          p"case object ${ccd.id}"
        } else {
          p"case class ${ccd.id}"
        }

        p"${nary(ccd.tparams, ", ", "[", "]")}"

        if (!ccd.isCaseObject) {
          p"(${ccd.fields})"
        }

        ccd.parent.foreach { par =>
          // Remember child and parents tparams are simple bijection
          p" extends ${par.id}${nary(ccd.tparams, ", ", "[", "]")}"
        }

        if (ccd.methods.nonEmpty) {
          p"""| {
              |  ${nary(ccd.methods, "\n\n")}
              |}"""
        }

      case fd: FunDef =>
        for (an <- fd.annotations) {
          p"""|@$an
              |"""
        }

        if (fd.canBeStrictField) {
          p"val ${fd.id} : "
        } else if (fd.canBeLazyField) {
          p"lazy val ${fd.id} : "
        } else {
          p"def ${fd.id}${nary(fd.tparams, ", ", "[", "]")}(${fd.params}): "
        }
        if (fd.decreaseMeasure.isDefined) {
          p"""${fd.returnType} = {
            | decreases(${fd.decreaseMeasure.get}) ${fd.fullBody} }"""
        } else
          p"${fd.returnType} = ${fd.fullBody}"

      case (tree: PrettyPrintable) => tree.printWith(ctx)

      case _                       => sb.append("Tree? (" + tree.getClass + ")")
    }
    if (opts.printTypes) {
      tree match {
        case t: Expr =>
          p" : ${t.getType} ⟩"

        case _ =>
      }
    }
    if (opts.printPositions) {
      tree.getPos match {
        case op: OffsetPosition =>
          p"@($op)"
        case rp: RangePosition =>
          if (rp.lineFrom == rp.lineTo) {
            if (rp.colFrom == rp.colTo) {
              p"@(${rp.lineFrom}:${rp.colFrom})"
            } else {
              p"@(${rp.lineFrom}:${rp.colFrom}-${rp.colTo})"
            }
          } else {
            p"@(${rp.focusBegin}-${rp.focusEnd})"
          }
        case _ =>
          p"@(?)"
      }
    }

  }

  protected object FcallMethodInvocation {
    def unapply(fi: FunctionInvocation): Option[(Expr, FunDef, Identifier, Seq[TypeTree], Seq[Expr])] = {
      val FunctionInvocation(tfd, args) = fi
      tfd.fd.methodOwner.map { cd =>
        val (rec, rargs) = (args.head, args.tail)

        val fid = tfd.fd.id

        val realtps = tfd.tps.drop(cd.tparams.size)

        (rec, tfd.fd, fid, realtps, rargs)
      }
    }
  }

  protected object BinaryMethodCall {
    val makeBinary = Set("+", "-", "*", "::", "++", "--", "&&", "||", "/")

    def unapply(fi: FunctionInvocation): Option[(Expr, String, Expr)] = fi match {
      case FcallMethodInvocation(rec, fd, id, Nil, List(a)) if (fd.annotations.contains("library") || !(opts.printRunnableCode)) =>
        val name = id.name
        if (makeBinary contains name) {
          if (name == "::")
            Some((a, name, rec))
          else
            Some((rec, name, a))
        } else {
          None
        }
      case _ => None
    }
  }

  protected def isSimpleExpr(e: Expr): Boolean = e match {
    case _: LetDef | _: Let | LetPattern(_, _, _) | _: Assert | _: Require => false
    case p: PrettyPrintable => p.isSimpleExpr
    case _ => true
  }

  protected def noBracesSub(e: Expr): Seq[Expr] = e match {
    case Assert(_, _, bd)                   => Seq(bd)
    case Let(_, _, bd)                      => Seq(bd)
    case xlang.Expressions.LetVar(_, _, bd) => Seq(bd)
    case LetDef(_, bd)                      => Seq(bd)
    case LetPattern(_, _, bd)               => Seq(bd)
    case Require(_, bd)                     => Seq(bd)
    case IfExpr(_, t, e)                    => Seq(t, e) // if-else always has braces anyway
    case Ensuring(bd, pred)                 => Seq(bd, pred)
    case _                                  => Seq()
  }

  protected def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (e: Expr, _) if isSimpleExpr(e) => false
    case (e: Expr, Some(within: Expr)) if noBracesSub(within) contains e => false
    case (_: Expr, Some(_: MatchCase)) => false
    case (_: LetDef, Some(_: LetDef)) => false
    case (e: Expr, Some(LetPattern(_, _, _))) => false
    case (_: Expr, Some(_: xlang.Expressions.Block)) => false
    case (_: xlang.Expressions.Block, Some(_: xlang.Expressions.While)) => false
    case (_: xlang.Expressions.Block, Some(_: FunDef)) => false
    case (_: xlang.Expressions.Block, Some(_: LetDef)) => false
    case (e: Expr, Some(_)) => true
    case _ => false
  }

  protected def precedence(ex: Expr): Int = ex match {
    case (pa: PrettyPrintable) => pa.printPrecedence
    case (_: ElementOfSet) => 0
    case (_: Modulo) => 1
    case (_: Or | BinaryMethodCall(_, "||", _)) => 2
    case (_: And | BinaryMethodCall(_, "&&", _)) => 3
    case (_: GreaterThan | _: GreaterEquals | _: LessEquals | _: LessThan | _: Implies) => 4
    case (_: Equals | _: Not) => 5
    case (_: Plus | _: BVPlus | _: Minus | _: BVMinus | _: SetUnion | _: SetDifference | BinaryMethodCall(_, "+" | "-", _)) => 7
    case (_: Times | _: BVTimes | _: Division | _: BVDivision | _: Remainder | _: BVRemainder | BinaryMethodCall(_, "*" | "/", _)) => 8
    case _ => 9
  }

  protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (pa: PrettyPrintable, _) => pa.printRequiresParentheses(within)
    case (_, None)                => false
    case (_, Some(
      _: Ensuring | _: Assert | _: Require | _: Definition | _: MatchExpr | _: MatchCase |
      _: Let | _: LetDef | _: IfExpr | _: CaseClass | _: Lambda | _: Choose | _: Tuple
      )) => false
    case (_: Pattern, _) => false
    case (ex: StringConcat, Some(_: StringConcat)) => false
    case (b1 @ BinaryMethodCall(_, _, _), Some(b2 @ BinaryMethodCall(_, _, _))) if precedence(b1) > precedence(b2) => false
    case (BinaryMethodCall(_, _, _), Some(_: FunctionInvocation)) => true
    case (_, Some(_: FunctionInvocation)) => false
    case (ie: IfExpr, _) => true
    case (me: MatchExpr, _) => true
    case (e1: Expr, Some(e2: Expr)) if precedence(e1) > precedence(e2) => false
    case (_, _) => true
  }
}

trait PrettyPrintable {
  self: Tree =>

  def printWith(implicit pctx: PrinterContext): Unit

  def printPrecedence: Int = 1000
  def printRequiresParentheses(within: Option[Tree]): Boolean = false
  def isSimpleExpr: Boolean = false
}

class EquivalencePrettyPrinter(opts: PrinterOptions, opgm: Option[Program]) extends PrettyPrinter(opts, opgm) {
  override def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = {
    tree match {
      case id: Identifier =>
        p"${id.name}"

      case _ =>
        super.pp(tree)
    }
  }
}

abstract class PrettyPrinterFactory {
  def create(opts: PrinterOptions, opgm: Option[Program]): PrettyPrinter

  def apply(tree: Tree, opts: PrinterOptions = PrinterOptions(), opgm: Option[Program] = None): String = {
    val printer = create(opts, opgm)
    val ctx = PrinterContext(tree, Nil, opts.baseIndent, printer)
    printer.pp(tree)(ctx)
    printer.toString
  }

  def apply(tree: Tree, ctx: LeonContext): String = {
    val opts = PrinterOptions.fromContext(ctx)
    apply(tree, opts, None)
  }

  def apply(tree: Tree, ctx: LeonContext, pgm: Program): String = {
    val opts = PrinterOptions.fromContext(ctx)
    apply(tree, opts, Some(pgm))
  }

}

object PrettyPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions, opgm: Option[Program]) = new PrettyPrinter(opts, opgm)
}

object EquivalencePrettyPrinter extends PrettyPrinterFactory {
  def create(opts: PrinterOptions, opgm: Option[Program]) = new EquivalencePrettyPrinter(opts, opgm)
}
