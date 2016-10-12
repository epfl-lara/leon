/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

private[genc] trait Builder {
  this: CConverter =>

  def buildVar(id: Identifier, typ: TypeTree)(implicit funCtx: FunCtx) =
    CAST.Var(convertToId(id), convertToType(typ))

  def buildVal(id: Identifier, typ: TypeTree)(implicit funCtx: FunCtx) =
    CAST.Val(convertToId(id), convertToType(typ))

  def buildAccessVar(id1: Identifier)(implicit funCtx: FunCtx) = {
    // Depending on the context, we have to deference the variable
    val id = convertToId(id1)
    if (funCtx.hasOuterVar(id)) CAST.AccessRef(id)
    else                        CAST.AccessVar(id)
  }

  def buildLet(id: Identifier, value: Expr, rest1: Expr, forceVar: Boolean)
              (implicit funCtx: FunCtx): CAST.Stmt = {
    // Handle special case with Unit: don't create a var
    if (value.getType == UnitType) convertToStmt(value) ~ convertToStmt(rest1)
    else {
      val (x, stmt) = buildDeclInitVar(id, value, forceVar)

      // Augment ctx for the following instructions
      val funCtx2 = funCtx.extend(x)
      val rest    = convertToStmt(rest1)(funCtx2)

      stmt ~ rest
    }
  }

  // Create a new variable for the given value, potentially immutable, and initialize it
  def buildDeclInitVar(id: Identifier, v: Expr, forceVar: Boolean)
                      (implicit funCtx: FunCtx): (CAST.Var, CAST.Stmt) = {
    val valueF = convertAndFlatten(v)
    val typ    = v.getType

    valueF.value match {
      case CAST.IfElse(cond, thn, elze) =>
        val x      = buildVar(id, typ)
        val decl   = CAST.DeclVar(x)
        val ifelse = buildIfElse(cond, injectAssign(x, thn), injectAssign(x, elze))
        val init   = decl ~ ifelse

        (x, valueF.body ~~ init)

      case value =>
        val x    = if (forceVar) buildVar(id, typ) else buildVal(id, typ)
        val init = CAST.DeclInitVar(x, value)

        (x, valueF.body ~~ init)
    }
  }

  def buildBinOp(lhs: Expr, op: String, rhs: Expr)(implicit funCtx: FunCtx) = {
    buildMultiOp(op, lhs :: rhs :: Nil)
  }

  def buildBinOp(lhs: CAST.Stmt, op: String, rhs: CAST.Stmt) = {
    CAST.Op(op, lhs, rhs)
  }

  def buildUnOp(op: String, rhs1: Expr)(implicit funCtx: FunCtx) = {
    val rhsF = convertAndFlatten(rhs1)
    rhsF.body ~~ CAST.Op(op, rhsF.value)
  }

  def buildMultiOp(op: String, exprs: Seq[Expr])(implicit funCtx: FunCtx): CAST.Stmt = {
    require(exprs.length >= 2)

    val stmts = exprs map convertToStmt
    val types = exprs map { e => convertToType(e.getType) }

    buildMultiOp(op, stmts, types)
  }

  def buildMultiOp(op: String, stmts: Seq[CAST.Stmt], types: Seq[CAST.Type]): CAST.Stmt = {
      // Default operator constuction when either pure statements are involved
      // or no shortcut can happen
      def defaultBuild = {
        val fs = normaliseExecution(stmts, types)
        fs.bodies ~~ CAST.Op(op, fs.values)
      }

      if (stmts forall { _.isPureValue }) defaultBuild
      else op match {
      case "&&" =>
        // Apply short-circuit if needed
        if (stmts.length == 2) {
          // Base case:
          // { { a; v } && { b; w } }
          // is mapped onto
          // { a; if (v) { b; w } else { false } }
          val av = flatten(stmts(0))
          val bw = stmts(1)

          if (bw.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, bw, CAST.False)
        } else {
          // Recursive case:
          // { { a; v } && ... }
          // is mapped onto
          // { a; if (v) { ... } else { false } }
          val av = flatten(stmts(0))
          val rest = buildMultiOp(op, stmts.tail, types.tail)

          if (rest.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, rest, CAST.False)
        }

      case "||" =>
        // Apply short-circuit if needed
        if (stmts.length == 2) {
          // Base case:
          // { { a; v } || { b; w } }
          // is mapped onto
          // { a; if (v) { true } else { b; w } }
          val av = flatten(stmts(0))
          val bw = stmts(1)

          if (bw.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, CAST.True, bw)
        } else {
          // Recusrive case:
          // { { a; v } || ... }
          // is mapped onto
          // { a; if (v) { true } else { ... } }
          val av = flatten(stmts(0))
          val rest = buildMultiOp(op, stmts.tail, types.tail)

          if (rest.isPureValue) defaultBuild
          else av.body ~~ buildIfElse(av.value, CAST.True, rest)
        }

      case _ =>
        defaultBuild
    }
  }

  // Flatten `if (if (cond1) thn1 else elze1) thn2 else elze2`
  // into `if (cond1) { if (thn1) thn2 else elz2 } else { if (elz1) thn2 else elze2 }`
  // or, if possible, into `if ((cond1 && thn1) || elz1) thn2 else elz2`
  //
  // Flatten `if (true) thn else elze` into `thn`
  // Flatten `if (false) thn else elze` into `elze`
  def buildIfElse(cond: CAST.Stmt, thn2: CAST.Stmt, elze2: CAST.Stmt): CAST.Stmt = {
    val condF = flatten(cond)

    val ifelse = condF.value match {
      case CAST.IfElse(cond1, thn1, elze1) =>
        if (cond1.isPure && thn1.isPure && elze1.isPure) {
          val bools = CAST.Bool :: CAST.Bool :: Nil
          val ands  = cond1 :: thn1 :: Nil
          val ors   = buildMultiOp("&&", ands, bools) :: elze1 :: Nil
          val condX = buildMultiOp("||", ors, bools)
          CAST.IfElse(condX, thn2, elze2)
        } else {
          buildIfElse(cond1, buildIfElse(thn1, thn2, elze2), buildIfElse(elze1, thn2, elze2))
        }

      case CAST.True  => thn2
      case CAST.False => elze2
      case cond2      => CAST.IfElse(cond2, thn2, elze2)
    }

    condF.body ~~ ifelse
  }

  def injectReturn(stmt: CAST.Stmt): CAST.Stmt = {
    val f = flatten(stmt)

    f.value match {
      case CAST.IfElse(cond, thn, elze) =>
        f.body ~~ CAST.IfElse(cond, injectReturn(thn), injectReturn(elze))

      // FIXME this is an hugly hack. Fix it when Error are supported in `convert`
      case CAST.NoStmt =>
        f.body ~~ CAST.NoStmt

      case _ =>
        f.body ~~ CAST.Return(f.value)
    }
  }

  def injectAssign(x: CAST.Var, stmt: CAST.Stmt): CAST.Stmt = {
    injectAssign(CAST.AccessVar(x.id), stmt)
  }

  def injectAssign(x: CAST.Stmt, stmt: CAST.Stmt): CAST.Stmt = {
    val f = flatten(stmt)

    f.value match {
      case CAST.IfElse(cond, thn, elze) =>
        f.body ~~ CAST.IfElse(cond, injectAssign(x, thn), injectAssign(x, elze))

      case _ =>
        f.body ~~ CAST.Assign(x, f.value)
    }
  }

}

