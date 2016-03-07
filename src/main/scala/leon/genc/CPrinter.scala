/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import CAST._
import CPrinterHelpers._

class CPrinter(val sb: StringBuffer = new StringBuffer) {
  override def toString = sb.toString

  def print(tree: Tree) = pp(tree)(PrinterContext(0, this))

  def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    /* ---------------------------------------------------------- Types ----- */
    case typ: Type => c"${typ.toString}"


    /* ------------------------------------------------------- Literals ----- */
    case IntLiteral(v) => c"$v"
    case BoolLiteral(b) => c"$b"


    /* --------------------------------------------------- Definitions  ----- */
    case Prog(structs, functions) =>
      c"""|/* ------------------------------------ includes ----- */
          |
          |${nary(includeStmts, sep = "\n")}
          |
          |/* ---------------------- data type declarations ----- */
          |
          |${nary(structs map StructDecl, sep = "\n")}
          |
          |/* ----------------------- data type definitions ----- */
          |
          |${nary(structs map StructDef, sep = "\n")}
          |
          |/* ----------------------- function declarations ----- */
          |
          |${nary(functions map FunDecl, sep = "\n")}
          |
          |/* ------------------------ function definitions ----- */
          |
          |${nary(functions, sep = "\n")}
          |"""

    case f @ Fun(_, _, _, body) =>
      c"""|${FunSign(f)}
          |{
          |  $body
          |}
          |"""

    case Id(name) => c"$name"


    /* --------------------------------------------------------- Stmts  ----- */
    case NoStmt => c"/* empty */"

    case Compound(stmts) =>
      val lastIdx = stmts.length - 1

      for ((stmt, idx) <- stmts.zipWithIndex) {
        if (stmt.isValue) c"$stmt;"
        else              c"$stmt"

        if (idx != lastIdx)
          c"$NewLine"
      }

    case Assert(pred, Some(error)) => c"assert($pred); /* $error */"
    case Assert(pred, None)        => c"assert($pred);"

    case Var(id, _) => c"$id"
    case DeclVar(Var(id, typ)) => c"$typ $id;"

    // If the length is a literal we don't need VLA
    case DeclInitVar(Var(id, typ), ai @ ArrayInit(IntLiteral(length), _, _)) =>
      val buffer = FreshId("buffer")
      val values = for (i <- 0 until length) yield ai.defaultValue
      c"""|${ai.valueType} $buffer[${ai.length}] = { $values };
          |$typ $id = { .length = ${ai.length}, .data = $buffer };
          |"""

    // TODO depending on the type of array (e.g. `char`) or the value (e.g. `0`), we could use `memset`.
    case DeclInitVar(Var(id, typ), ai: ArrayInit) => // Note that `typ` is a struct here
      val buffer = FreshId("vla_buffer")
      val i = FreshId("i")
      c"""|${ai.valueType} $buffer[${ai.length}];
          |for (${Int32} $i = 0; $i < ${ai.length}; ++$i) {
          |  $buffer[$i] = ${ai.defaultValue};
          |}
          |$typ $id = { .length = ${ai.length}, .data = $buffer };
          |"""

    case DeclInitVar(Var(id, typ), ai: ArrayInitWithValues) => // Note that `typ` is a struct here
      val buffer = FreshId("buffer")
      c"""|${ai.valueType} $buffer[${ai.length}] = { ${ai.values} };
          |$typ $id = { .length = ${ai.length}, .data = $buffer };
          |"""

    case DeclInitVar(Var(id, typ), value) =>
      c"$typ $id = $value;"

    case Assign(lhs, rhs) =>
      c"$lhs = $rhs;"

    case UnOp(op, rhs) => c"($op$rhs)"
    case MultiOp(op, stmts) => c"""${nary(stmts, sep = s" ${op.fixMargin} ",
                                          opening = "(", closing = ")")}"""
    case SubscriptOp(ptr, idx) => c"$ptr[$idx]"

    case Break => c"break;"
    case Return(stmt) => c"return $stmt;"

    case IfElse(cond, thn, elze) =>
      c"""|if ($cond)
          |{
          |  $thn
          |}
          |else
          |{
          |  $elze
          |}
          |"""

    case While(cond, body) =>
      c"""|while ($cond)
          |{
          |  $body
          |}
          |"""

    case AccessVar(id)              => c"$id"
    case AccessRef(id)              => c"(*$id)"
    case AccessAddr(id)             => c"(&$id)"
    case AccessField(struct, field) => c"$struct.$field"
    case Call(id, args)             => c"$id($args)"

    case StructInit(args, struct) =>
      c"(${struct.id}) { "
      for ((id, stmt) <- args.init) {
        c".$id = $stmt, "
      }
      if (!args.isEmpty) {
        val (id, stmt) = args.last
        c".$id = $stmt "
      }
      c"}"

    /* --------------------------------------------------------- Error  ----- */
    case tree => sys.error(s"CPrinter: <<$tree>> was not handled properly")
  }


  def pp(wt: WrapperTree)(implicit ctx: PrinterContext): Unit = wt match {
    case FunDecl(f) =>
      c"${FunSign(f)};$NewLine"

    case FunSign(Fun(id, retType, Nil, _)) =>
      c"""|$retType
          |$id($Void)"""

    case FunSign(Fun(id, retType, params, _)) =>
      c"""|$retType
          |$id(${nary(params map DeclParam)})"""

    case DeclParam(Var(id, typ)) =>
      c"$typ $id"

    case StructDecl(s) =>
      c"struct $s;"

    case StructDef(Struct(name, fields)) =>
      c"""|typedef struct $name {
          |  ${nary(fields map DeclParam, sep = ";\n", closing = ";")}
          |} $name;
          |"""

    case NewLine =>
      c"""|
          |"""
  }

  /** Hardcoded list of required include files from C standard library **/
  lazy val includes = "assert.h" :: "stdbool.h" :: "stdint.h" :: Nil
  lazy val includeStmts = includes map { i => s"#include <$i>" }

  /** Wrappers to distinguish how the data should be printed **/
  sealed abstract class WrapperTree
  case class FunDecl(f: Fun) extends WrapperTree
  case class FunSign(f: Fun) extends WrapperTree
  case class DeclParam(x: Var) extends WrapperTree
  case class StructDecl(s: Struct) extends WrapperTree
  case class StructDef(s: Struct) extends WrapperTree
  case object NewLine extends WrapperTree
}

