/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import leon.purescala.Common._
import leon.purescala.DefOps._
import leon.purescala.Definitions._
import leon.purescala.Extractors._
import leon.purescala.PrinterHelpers._
import leon.purescala.ExprOps.{isListLiteral, simplestValue}
import leon.purescala.Expressions._
import leon.purescala.TypeOps.leastUpperBound
import leon.purescala.Types._
import leon.synthesis.Witnesses._

case class PrinterContext(
  current: Tree,
  parent: Option[Tree],
  scope : Option[Definition],
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

      val strings     = sc.parts.iterator
      val expressions = args.iterator

      var extraInd = 0
      var firstElem = true

      while(strings.hasNext) {
        val s = strings.next.stripMargin

        // Compute indentation
        val start = s.lastIndexOf('\n')
        if(start >= 0 || firstElem) {
          var i = start+1
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
              val newScope = nctx.current match { 
                case d : Definition => Some(d)
                case _ => nctx.scope 
              }
              nctx = nctx.copy(current = t, parent = Some(nctx.current), scope = newScope)
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
      p"$t : ${t.getType}"
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
  
  def printWithPath(df: Definition)(implicit ctx : PrinterContext) {
    ctx.scope match {
      case Some(scope) => 
        try {
          val (pack, defPath) = pathAsVisibleFrom(scope, df)
          val toPrint = pack ++ (defPath collect { case df if !df.isInstanceOf[UnitDef] => df.id})
          p"${nary(toPrint, ".")}"
        } catch {
          // If we did not manage to find the path, just print the id
          case _ : NoSuchElementException => p"${df.id}"
        }
      case None =>
        p"${df.id}"
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
          s"$alphaNumDollar+|[$alphaNumDollar+_]?[!@#%^&*+-\\|~/?><:]+"
        )
        // Replace $opname with operator symbols
        val candidate = scala.reflect.NameTransformer.decode(name)
        
        if (isLegalScalaId(candidate)) p"$candidate" else p"$name"
        
      case Variable(id) =>
        p"$id"

      case Let(b,d,e) =>
        optB { e match {
          case _:LetDef | _ : Let | LetPattern(_,_,_) =>
            p"""|val $b = {
                |  $d
                |}
                |$e"""
          case _ =>
            p"""|val $b = $d;
                |$e"""
        }}
      case LetDef(fd,body) =>
        optB {
          p"""|$fd
              |$body"""
        }

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
        p"""|{
            |  $body
            |} ensuring {
            |  $post
            |}"""

      case Gives(s, tests) => 
        optP {
          p"""|$s gives {
              |  ${nary(tests, "\n")}
              |}"""
        }
      
      case p@Passes(in, out, tests) =>
        optP {
          p"""|($in, $out) passes {
              |  ${nary(tests, "\n")}
              |}"""
        }

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
      case e @ CaseClass(cct, args) =>
        isListLiteral(e) match {
          case Some((tpe, elems)) =>
            val chars = elems.collect{case CharLiteral(ch) => ch}
            if (chars.length == elems.length && tpe == CharType) {
              // String literal
              val str = chars mkString ""
              val q = '"'
              p"$q$str$q"
            } else {
              val elemTps = leastUpperBound(elems.map(_.getType))
              if (elemTps == Some(tpe)) {
                p"List($elems)"  
              } else {
                p"List[$tpe]($elems)"  
              }
            }

            case None =>
              if (cct.classDef.isCaseObject) {
                p"$cct"
              } else {
                p"$cct($args)"
              }
        }




      case And(exprs)           => optP { p"${nary(exprs, " && ")}" }
      case Or(exprs)            => optP { p"${nary(exprs, "| || ")}" }
      case Not(Equals(l, r))    => optP { p"$l \u2260 $r" }
      case Implies(l,r)         => optP { p"$l ==> $r" }
      case UMinus(expr)         => p"-$expr"
      case BVUMinus(expr)       => p"-$expr"
      case Equals(l,r)          => optP { p"$l == $r" }
      case IntLiteral(v)        => p"$v"
      case InfiniteIntegerLiteral(v)        => p"$v"
      case CharLiteral(v)       => p"$v"
      case BooleanLiteral(v)    => p"$v"
      case UnitLiteral()        => p"()"
      case GenericValue(tp, id) => p"$tp#$id"
      case Tuple(exprs)         => p"($exprs)"
      case TupleSelect(t, i)    => p"$t._$i"
      case NoTree(tpe)          => p"???($tpe)"
      case Choose(pred, oimpl) => 
        oimpl match {
          case Some(e) =>
            p"$e /* choose: $pred */"
          case None =>
            p"choose($pred)"
        }
      case e @ Error(tpe, err)       => p"""error[$tpe]("$err")"""
      case CaseClassInstanceOf(cct, e)         =>
        if (cct.classDef.isCaseObject) {
          p"($e == $cct)"
        } else {
          p"$e.isInstanceOf[$cct]"
        }
      case CaseClassSelector(_, e, id)         => p"$e.$id"
      case MethodInvocation(rec, _, tfd, args) =>
        p"$rec.${tfd.id}"

        if (tfd.tps.nonEmpty) {
          p"[${tfd.tps}]"
        }

        // No () for fields
        if (tfd.fd.isRealFunction) {
          // The non-present arguments are synthetic function invocations
          val presentArgs = args filter {
            case MethodInvocation(_, _, tfd, _) if tfd.fd.isSynthetic => false
            case FunctionInvocation(tfd, _)     if tfd.fd.isSynthetic => false
            case other => true
          }
          p"($presentArgs)"
        }

      case BinaryMethodCall(a, op, b) =>
        optP { p"$a $op $b" }

      case FcallMethodInvocation(rec, fd, id, tps, args) =>

        p"$rec.$id"
        if (tps.nonEmpty) {
          p"[$tps]"
        }

        if (fd.isRealFunction) {
          // The non-present arguments are synthetic function invocations
          val presentArgs = args filter {
            case MethodInvocation(_, _, tfd, _) if tfd.fd.isSynthetic => false
            case FunctionInvocation(tfd, _)     if tfd.fd.isSynthetic => false
            case other => true
          }
          p"($presentArgs)"
        }

      case FunctionInvocation(tfd, args) =>
        p"${tfd.id}"

        if (tfd.tps.nonEmpty) {
          p"[${tfd.tps}]"
        }

        if (tfd.fd.isRealFunction) { 
          // The non-present arguments are synthetic function invocations
          val presentArgs = args filter {
            case MethodInvocation(_, _, tfd, _) if tfd.fd.isSynthetic => false
            case FunctionInvocation(tfd, _)     if tfd.fd.isSynthetic => false
            case other => true
          }
          p"($presentArgs)"
        }

      case Application(caller, args) =>
        p"$caller($args)"

      case Lambda(args, body) =>
        optP { p"($args) => $body" }

      case Plus(l,r)                 => optP { p"$l + $r" }
      case Minus(l,r)                => optP { p"$l - $r" }
      case Times(l,r)                => optP { p"$l * $r" }
      case Division(l,r)             => optP { p"$l / $r" }
      case Modulo(l,r)               => optP { p"$l % $r" }
      case LessThan(l,r)             => optP { p"$l < $r" }
      case GreaterThan(l,r)          => optP { p"$l > $r" }
      case LessEquals(l,r)           => optP { p"$l <= $r" }
      case GreaterEquals(l,r)        => optP { p"$l >= $r" }
      case BVPlus(l,r)               => optP { p"$l + $r" }
      case BVMinus(l,r)              => optP { p"$l - $r" }
      case BVTimes(l,r)              => optP { p"$l * $r" }
      case BVDivision(l,r)           => optP { p"$l / $r" }
      case BVModulo(l,r)             => optP { p"$l % $r" }
      case BVAnd(l,r)                => optP { p"$l & $r" }
      case BVOr(l,r)                 => optP { p"$l | $r" }
      case BVXOr(l,r)                => optP { p"$l ^ $r" }
      case BVShiftLeft(l,r)          => optP { p"$l << $r" }
      case BVAShiftRight(l,r)        => optP { p"$l >> $r" }
      case BVLShiftRight(l,r)        => optP { p"$l >>> $r" }
      case fs @ FiniteSet(rs)        => p"{${rs.toSeq}}"
      case fm @ FiniteMap(rs)        => p"{$rs}"
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
      case ArraySelect(a, i)         => p"$a($i)"
      case ArrayUpdated(a, i, v)     => p"$a.updated($i, $v)"
      case a@FiniteArray(es, d, s)   => {
        val ArrayType(underlying) = a.getType
        val default = d.getOrElse(simplestValue(underlying))
        def ppBigArray(): Unit = {
          if(es.isEmpty) {
            p"Array($default, $default, $default, ..., $default) (of size $s)"
          } else {
            p"Array(_) (of size $s)"
          }
        }
        s match {
          case IntLiteral(length) => {
            if(es.size == length) {
              val orderedElements = es.toSeq.sortWith((e1, e2) => e1._1 < e2._1).map(el => el._2)
              p"Array($orderedElements)"
            } else if(length < 10) {
              val elems = (0 until length).map(i => 
                es.find(el => el._1 == i).map(el => el._2).getOrElse(d.get)
              )
              p"Array($elems)"
            } else {
              ppBigArray()
            }
          }
          case _ => ppBigArray()
        }
      }

      case Not(expr)                 => p"\u00AC$expr"
      case vd@ValDef(id, _)          => vd.defaultValue match {
        case Some(fd) => p"$id : ${vd.getType} = ${fd.body.get}"
        case None => p"$id : ${vd.getType}"
      }
      case This(_)                   => p"this"
      case (tfd: TypedFunDef)        => p"typed def ${tfd.id}[${tfd.tps}]"
      case TypeParameterDef(tp)      => p"$tp"
      case TypeParameter(id)         => p"$id"


      case IfExpr(c, t, ie : IfExpr) =>
        optP {
          p"""|if ($c) {
              |  $t
              |} else $ie"""
        }

      case Terminating(tfd, args) =>
        p"↓ ${tfd.id}($args)"

      case Guide(e) =>
        p"⊙ {$e}"

      case IfExpr(c, t, e) =>
        optP {
          p"""|if ($c) {
              |  $t
              |} else {
              |  $e
              |}"""
        }

      case LetPattern(p,s,rhs) => 
        rhs match { 
          case _:LetDef | _ : Let | LetPattern(_,_,_) =>
            optP {
              p"""|val $p = {
                  |  $s
                  |}
                  |$rhs"""
            }

          case _ => 
            optP {
              p"""|val $p = $s
                  |$rhs"""
            }
        }

      case MatchExpr(s, csc) =>
        optP {
          p"""|$s match {
              |  ${nary(csc, "\n")}
              |}"""
        }

      // Cases
      case MatchCase(pat, optG, rhs) =>
        p"|case $pat "; optG foreach { g => p"if $g "}; p"""=>
          |  $rhs"""

      // Patterns
      case WildcardPattern(None)     => p"_"
      case WildcardPattern(Some(id)) => p"$id"

      case CaseClassPattern(ob, cct, subps) =>
        // TODO specialize for strings
        ob.foreach { b => p"$b @ " }
        // Print only the classDef because we don't want type parameters in patterns
        printWithPath(cct.classDef)
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

      case LiteralPattern(ob, lit) =>
        ob foreach { b => p"$b @ " }
        p"$lit"

      // Types
      case Untyped               => p"<untyped>"
      case UnitType              => p"Unit"
      case Int32Type             => p"Int"
      case IntegerType           => p"BigInt"
      case CharType              => p"Char"
      case BooleanType           => p"Boolean"
      case ArrayType(bt)         => p"Array[$bt]"
      case SetType(bt)           => p"Set[$bt]"
      case MapType(ft,tt)        => p"Map[$ft, $tt]"
      case MultisetType(bt)      => p"Multiset[$bt]"
      case TupleType(tpes)       => p"($tpes)"
      case FunctionType(fts, tt) => p"($fts) => $tt"
      case c: ClassType =>
        printWithPath(c.classDef)
        if (c.tps.nonEmpty) {
          p"[${c.tps}]"
        }

      // Definitions
      case Program(id, units) =>
        p"""${nary(units filter {_.isMainUnit}, "\n\n")}"""
      
      case UnitDef(id,modules,pack,imports,_) =>
        if (pack.nonEmpty){
          p"""|package ${pack mkString "."}
              |"""
        }
        p"""|${nary(imports,"\n")}
            |${nary(modules,"\n\n")}
            |"""
        
      case PackageImport(pack) => 
        import leon.purescala.DefOps._
        val newPack = ( for (
          scope <- ctx.scope;
          unit <- unitOf(scope);
          currentPack = unit.pack
        ) yield {  
          if (isSuperPackageOf(currentPack,pack)) 
            pack drop currentPack.length
          else 
            pack
        }).getOrElse(pack)
        p"import ${nary(newPack,".")}._"

      case SingleImport(df) => 
        p"import "; printWithPath(df)
         
        
      case WildcardImport(df) => 
        p"import "; printWithPath(df); p"._"
        
      case ModuleDef(id, defs, _) =>
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

        if (fd.canBeField) {
          p"""|${fd.defType} ${fd.id} : ${fd.returnType} = {
              |"""
        } else if (fd.tparams.nonEmpty) {
          p"""|def ${fd.id}[${nary(fd.tparams, ",")}](${fd.params}): ${fd.returnType} = {
              |"""
        } else {
          p"""|def ${fd.id}(${fd.params}): ${fd.returnType} = {
              |"""
        }
          
        
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

        fd.postcondition.foreach { post =>
          p"""| ensuring {
              |  $post
              |}"""
        }

      case (tree: PrettyPrintable) => tree.printWith(ctx)

      case _ => sb.append("Tree? (" + tree.getClass + ")")
    
  }

  object FcallMethodInvocation {
    def unapply(fi: FunctionInvocation): Option[(Expr, FunDef, String, Seq[TypeTree], Seq[Expr])] = {
        val FunctionInvocation(tfd, args) = fi
        tfd.fd.origOwner match {
          case Some(cd: ClassDef) =>
            val (rec, rargs) = (args.head, args.tail)

            val fid = tfd.fd.id

            val maybeClassName = fid.name.substring(0, cd.id.name.length)

            val fname = if (maybeClassName == cd.id.name) {
              fid.name.substring(cd.id.name.length + 1) // +1 to also remove $
            } else {
              fid.name
            }

            val decoded = scala.reflect.NameTransformer.decode(fname)

            val realtps = tfd.tps.drop(cd.tparams.size)

            Some((rec, tfd.fd, decoded, realtps, rargs))
          case _ =>
            None
        }
    }
  }

  object BinaryMethodCall {
    val makeBinary = Set("+", "-", "*", "::", "++", "--", "&&", "||", "/")

    def unapply(fi: FunctionInvocation): Option[(Expr, String, Expr)] = fi match {
      case FcallMethodInvocation(rec, _, name, Nil, List(a)) =>

        if (makeBinary contains name) {
          if(name == "::")
            Some((a, name, rec))
          else
            Some((rec, name, a))
        } else {
          None
        }
      case _ => None
    }
  }

  def requiresBraces(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (pa: PrettyPrintable, _) => pa.printRequiresBraces(within)
    case (_, None) => false
    case (_: LetDef, Some(_: FunDef)) => true
    case (_: Require, Some(_: Ensuring)) => false
    case (_: Require, _) => true
    case (_: Assert, Some(_: Definition)) => true
    case (_, Some(_: Definition)) => false
    case (_, Some(_: MatchExpr | _: MatchCase | _: Let | _: LetDef )) => false
    case (_, _) => true
  }

  def precedence(ex: Expr): Int = ex match {
    case (pa: PrettyPrintable) => pa.printPrecedence
    case (_: ElementOfSet) => 0
    case (_: Or | BinaryMethodCall(_, "||", _)) => 1
    case (_: And | BinaryMethodCall(_, "&&", _)) => 3
    case (_: GreaterThan | _: GreaterEquals  | _: LessEquals | _: LessThan) => 4
    case (_: Equals | _: Not) => 5
    case (_: Plus | _: BVPlus | _: Minus | _: BVMinus | _: SetUnion| _: SetDifference | BinaryMethodCall(_, "+" | "-", _)) => 6
    case (_: Times | _: BVTimes | _: Division | _: BVDivision | _: Modulo | _: BVModulo | BinaryMethodCall(_, "*" | "/", _)) => 7
    case _ => 7
  }

  def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (pa: PrettyPrintable, _) => pa.printRequiresParentheses(within)
    case (_, None) => false
    case (_, Some(_: Ensuring)) => false
    case (_, Some(_: Assert)) => false
    case (_, Some(_: Require)) => false
    case (_, Some(_: Definition)) => false
    case (_, Some(_: MatchExpr | _: MatchCase | _: Let | _: LetDef | _: IfExpr | _ : CaseClass)) => false
    case (b1 @ BinaryMethodCall(_, _, _), Some(b2 @ BinaryMethodCall(_, _, _))) if precedence(b1) > precedence(b2) => false
    case (BinaryMethodCall(_, _, _), Some(_: FunctionInvocation)) => true
    case (_, Some(_: FunctionInvocation)) => false
    case (ie: IfExpr, _) => true
    case (me: MatchLike, _ ) => true
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

  def apply(tree: Tree, opts: PrinterOptions = PrinterOptions(), scope : Option[Definition] = None): String = {
    val printer = create(opts)
    val scope_ = (tree, scope) match {
      // Try to find a scope, if we are given none.
      case (df : Definition, None) => df.owner
      case _ => None
    }
    val ctx = PrinterContext(tree, None, scope_, opts.baseIndent, printer)
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
