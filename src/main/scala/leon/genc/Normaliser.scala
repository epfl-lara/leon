/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc

import purescala.Expressions._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

private[genc] trait Normaliser {
  this: CConverter =>

  // Flattened represents a non-empty statement { a; b; ...; y; z }
  // split into body { a; b; ...; y } and value z
  case class Flattened(value: CAST.Stmt, body: Seq[CAST.Stmt])

  // FlattenedSeq does the same as Flattened for a sequence of non-empty statements
  case class FlattenedSeq(values: Seq[CAST.Stmt], bodies: Seq[CAST.Stmt])

  def flatten(stmt: CAST.Stmt) = stmt match {
    case CAST.Compound(stmts) if stmts.isEmpty => internalError(s"Empty compound cannot be flattened")
    case CAST.Compound(stmts)                  => Flattened(stmts.last, stmts.init)
    case stmt                                  => Flattened(stmt, Seq())
  }

  def convertAndFlatten(expr: Expr)(implicit funCtx: FunCtx) = flatten(convertToStmt(expr))

  // Normalise execution order of, for example, function parameters;
  // `types` represents the expected type of the corresponding values
  // in case an intermediary variable needs to be created
  def convertAndNormaliseExecution(exprs: Seq[Expr], types: Seq[CAST.Type])(implicit funCtx: FunCtx) = {
    require(exprs.length == types.length)
    normaliseExecution(exprs map convertToStmt, types)
  }

  def normaliseExecution(typedStmts: Seq[(CAST.Stmt, CAST.Type)]): FlattenedSeq =
    normaliseExecution(typedStmts map { _._1 }, typedStmts map { _._2 })

  def normaliseExecution(stmts: Seq[CAST.Stmt], types: Seq[CAST.Type]): FlattenedSeq = {
    require(stmts.length == types.length)

    // Create temporary variables if needed
    val stmtsFs = stmts map flatten
    val fs = (stmtsFs zip types) map {
      case (f, _) if f.value.isPureValue => f

      case (f, typ) =>
        // Similarly to buildDeclInitVar:
        val (tmp, body) = f.value match {
          case CAST.IfElse(cond, thn, elze) =>
            val tmp    = CAST.FreshVar(typ.removeConst, "normexec")
            val decl   = CAST.DeclVar(tmp)
            val ifelse = buildIfElse(cond, injectAssign(tmp, thn), injectAssign(tmp, elze))
            val body   = f.body ~~ decl ~ ifelse

            (tmp, body)

          case value =>
            val tmp  = CAST.FreshVal(typ, "normexec")
            val body = f.body ~~ CAST.DeclInitVar(tmp, f.value)

            (tmp, body)
        }

        val value = CAST.AccessVar(tmp.id)
        flatten(body ~ value)
    }

    val empty  = Seq[CAST.Stmt]()
    val bodies = fs.foldLeft(empty){ _ ++ _.body }
    val values = fs map { _.value }

    FlattenedSeq(values, bodies)
  }

}

