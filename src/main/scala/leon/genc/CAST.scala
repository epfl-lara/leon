/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import utils.UniqueCounter

/*
 * Here are defined classes used to represent AST of C programs.
 */

object CAST { // C Abstract Syntax Tree

  sealed abstract class Tree
  case object NoTree extends Tree


  /* ------------------------------------------------------------ Types ----- */
  abstract class Type(val rep: String) extends Tree {
    override def toString = rep

    def mutable: Type = this match {
      case Const(typ) => typ.mutable
      case _          => this
    }
  }

  /* Type Modifiers */
  case class Const(typ: Type) extends Type(s"$typ const")
  case class Pointer(typ: Type) extends Type(s"$typ*")

  /* Primitive Types */
  case object Int32 extends Type("int32_t") // Requires <stdint.h>
  case object Bool extends Type("bool")     // Requires <stdbool.h>
  case object Void extends Type("void")

  /* Compound Types */
  case class Struct(id: Id, fields: Seq[Var]) extends Type(id.name)


  /* --------------------------------------------------------- Literals ----- */
  case class IntLiteral(v: Int) extends Stmt
  case class BoolLiteral(b: Boolean) extends Stmt


  /* ----------------------------------------------------- Definitions  ----- */
  abstract class Def extends Tree

  case class Prog(structs: Seq[Struct], functions: Seq[Fun]) extends Def

  case class Fun(id: Id, retType: Type, params: Seq[Var], body: Stmt) extends Def

  case class Id(name: String) extends Def {
    // `|` is used as the margin delimiter and can cause trouble in some situations
    def fixMargin =
      if (name.size > 0 && name(0) == '|') "| " + name
      else name
  }

  case class Var(id: Id, typ: Type) extends Def

  /* ----------------------------------------------------------- Stmts  ----- */
  abstract class Stmt extends Tree
  case object NoStmt extends Stmt

  case class Compound(stmts: Seq[Stmt]) extends Stmt

  case class Assert(pred: Stmt, error: Option[String]) extends Stmt { // Requires <assert.h>
    require(pred.isValue)
  }

  case class DeclVar(x: Var) extends Stmt

  case class DeclInitVar(x: Var, value: Stmt) extends Stmt {
    require(value.isValue)
  }

  case class Assign(lhs: Stmt, rhs: Stmt) extends Stmt {
    require(lhs.isValue && rhs.isValue)
  }

  // Note: we don't need to differentiate between specific
  // operators so we only keep track of the "kind" of operator
  // with an Id.
  case class UnOp(op: Id, rhs: Stmt) extends Stmt {
    require(rhs.isValue)
  }

  case class MultiOp(op: Id, stmts: Seq[Stmt]) extends Stmt {
    require(stmts.length > 1 && stmts.forall { _.isValue })
  }

  case class SubscriptOp(ptr: Stmt, idx: Stmt) extends Stmt {
    require(ptr.isValue && idx.isValue)
  }

  case object Break extends Stmt

  case class Return(stmt: Stmt) extends Stmt {
    require(stmt.isValue)
  }

  case class IfElse(cond: Stmt, thn: Stmt, elze: Stmt) extends Stmt {
    require(cond.isValue)
  }

  case class While(cond: Stmt, body: Stmt) extends Stmt {
    require(cond.isValue)
  }

  case class AccessVar(id: Id) extends Stmt
  case class AccessRef(id: Id) extends Stmt
  case class AccessAddr(id: Id) extends Stmt
  case class AccessField(struct: Stmt, field: Id) extends Stmt {
    require(struct.isValue)
  }

  case class Call(id: Id, args: Seq[Stmt]) extends Stmt {
    require(args forall { _.isValue })
  }

  case class StructInit(args: Seq[(Id, Stmt)], struct: Struct) extends Stmt {
    require(args forall { _._2.isValue })
  }

  case class ArrayInit(length: Stmt, valueType: Type, defaultValue: Stmt) extends Stmt {
    require(length.isValue && defaultValue.isValue)
  }

  case class ArrayInitWithValues(valueType: Type, values: Seq[Stmt]) extends Stmt {
    require(values forall { _.isValue })

    lazy val length = values.length
  }


  /* -------------------------------------------------------- Factories ----- */
  object Op {
    def apply(op: String, rhs: Stmt) = UnOp(Id(op), rhs)
    def apply(op: String, rhs: Stmt, lhs: Stmt) = MultiOp(Id(op), rhs :: lhs :: Nil)
    def apply(op: String, stmts: Seq[Stmt]) = MultiOp(Id(op), stmts)
  }

  object Val {
    def apply(id: Id, typ: Type) = typ match {
      case Const(_) => Var(id, typ) // avoid const of const
      case _        => Var(id, Const(typ))
    }
  }

  /* "Templatetized" Types */
  object Tuple {
    def apply(bases: Seq[Type]) = {
      val name = Id("__leon_tuple_" + bases.mkString("_") + "_t")

      val fields = bases.zipWithIndex map {
        case (typ, idx) => Var(getNthId(idx + 1), typ)
      }

      Struct(name, fields)
    }

    // Indexes start from 1, not 0!
    def getNthId(n: Int) = Id("_" + n)
  }

  object Array {
    def apply(base: Type) = {
      val name   = Id("__leon_array_" + base + "_t")
      val data   = Var(dataId, Pointer(base))
      val length = Var(lengthId, Int32)
      val fields = data :: length :: Nil

      Struct(name, fields)
    }

    def lengthId = Id("length")
    def dataId   = Id("data")
  }


  /* ---------------------------------------------------- Introspection ----- */
  implicit class IntrospectionOps(val stmt: Stmt) {
    def isLiteral = stmt match {
      case _: IntLiteral  => true
      case _: BoolLiteral => true
      case _              => false
    }

    // True if statement can be used as a value
    def isValue: Boolean = isLiteral || {
      stmt match {
        //case _: Assign => true it's probably the case but for now let's ignore it
        case c: Compound            => c.stmts.size == 1 && c.stmts.head.isValue
        case _: UnOp                => true
        case _: MultiOp             => true
        case _: SubscriptOp         => true
        case _: AccessVar           => true
        case _: AccessRef           => true
        case _: AccessAddr          => true
        case _: AccessField         => true
        case _: Call                => true
        case _: StructInit          => true
        case _: ArrayInit           => true
        case _: ArrayInitWithValues => true
        case _                      => false
      }
    }

    def isPure: Boolean = isLiteral || {
      stmt match {
        case NoStmt                 => true
        case Compound(stmts)        => stmts forall { _.isPure }
        case Assert(pred, _)        => pred.isPure
        case UnOp(_, rhs)           => rhs.isPure
        case MultiOp(_, stmts)      => Compound(stmts).isPure
        case SubscriptOp(ptr, idx)  => (ptr ~ idx).isPure
        case IfElse(c, t, e)        => (c ~ t ~ e).isPure
        case While(c, b)            => (c ~ b).isPure
        case AccessVar(_)           => true
        case AccessRef(_)           => true
        case AccessAddr(_)          => true
        case AccessField(s, _)      => s.isPure
        // case Call(id, args)      => true if args are pure and function `id` is pure too
        case _                      => false
      }
    }

    def isPureValue = isValue && isPure
  }


  /* ------------------------------------------------------------- DSL  ----- */
  // Operator ~~ appends and flattens nested compounds
  implicit class StmtOps(val stmt: Stmt) {
    // In addition to combining statements together in a compound
    // we remove the empty ones and if the resulting compound
    // has only one statement we return this one without being
    // wrapped into a Compound
    def ~(other: Stmt) = {
      val stmts = (stmt, other) match {
        case (Compound(stmts), Compound(others)) => stmts ++ others
        case (stmt           , Compound(others)) => stmt  +: others
        case (Compound(stmts), other           ) => stmts :+ other
        case (stmt           , other           ) => stmt :: other :: Nil
      }

      def isNoStmt(s: Stmt) = s match {
        case NoStmt => true
        case _      => false
      }

      val compound = Compound(stmts filterNot isNoStmt)
      compound match {
        case Compound(stmts) if stmts.length == 0 => NoStmt
        case Compound(stmts) if stmts.length == 1 => stmts.head
        case compound                             => compound
      }
    }

    def ~~(others: Seq[Stmt]) = stmt ~ Compound(others)
  }

  implicit class StmtsOps(val stmts: Seq[Stmt]) {
    def ~~(other: Stmt) = other match {
      case Compound(others) => Compound(stmts) ~~ others
      case other            => Compound(stmts) ~ other
    }

    def ~~~(others: Seq[Stmt]) = Compound(stmts) ~~ others
  }

  val True = BoolLiteral(true)
  val False = BoolLiteral(false)


  /* ------------------------------------------------ Fresh Generators  ----- */
  object FreshId {
    private var counter = -1
    private val leonPrefix = "__leon_"

    def apply(prefix: String = ""): Id = {
      counter += 1
      Id(leonPrefix + prefix + counter)
    }
  }

  object FreshVar {
    def apply(typ: Type, prefix: String = "") = Var(FreshId(prefix), typ)
  }

  object FreshVal {
    def apply(typ: Type, prefix: String = "") = Val(FreshId(prefix), typ)
  }
}

