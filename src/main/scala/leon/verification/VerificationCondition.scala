/* Copyright 2009-2016 EPFL, Lausanne */

package leon.verification

import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.Types._
import leon.purescala.PrettyPrinter
import leon.purescala.ExprOps
import leon.utils.Positioned
import leon.solvers._
import leon.LeonContext
import leon.purescala.SelfPrettyPrinter

/** This is just to hold some history information. */
case class VC(condition: Expr, fd: FunDef, kind: VCKind) extends Positioned {
  override def toString = {
    fd.id.name +" - " +kind.toString
  }
  // If the two functions are the same but have different positions, used to transfer one to the other.
  def copyTo(newFun: FunDef) = {
    val thisPos = this.getPos
    val newPos = ExprOps.lookup(_.getPos == thisPos, _.getPos)(fd.fullBody, newFun.fullBody) match {
      case Some(position) => position
      case None => newFun.getPos
    }
    val newCondition = ExprOps.lookup(condition == _, i => i)(fd.fullBody, newFun.fullBody).getOrElse(condition)
    VC(newCondition, newFun, kind).setPos(newPos)
  }
}

abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name

  def underlying = this
}

object VCKinds {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k
  }

  case object Precondition    extends VCKind("precondition", "precond.")
  case object Postcondition   extends VCKind("postcondition", "postcond.")
  case object Assert          extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch extends VCKind("match exhaustiveness", "match.")
  case object MapUsage        extends VCKind("map usage", "map use")
  case object ArrayUsage      extends VCKind("array usage", "arr. use")
  case object DivisionByZero  extends VCKind("division by zero", "div 0")
  case object ModuloByZero    extends VCKind("modulo by zero", "mod 0")
  case object RemainderByZero extends VCKind("remainder by zero", "rem 0")
  case object CastError       extends VCKind("cast correctness", "cast")
  case object PostTactVC         extends VCKind("Postcondition Tactic", "tact")
  case object StrictArithmetic   extends VCKind("strict arithmetic", "arithmetic")
  case object ArithmeticOverflow extends VCKind("arithmetic overflow", "overflow")
}

case class VCResult(status: VCStatus, solvedWith: Option[Solver], timeMs: Option[Long]) {
  def isValid   = status == VCStatus.Valid
  def isInvalid = status.isInstanceOf[VCStatus.Invalid]
  def isInconclusive = !isValid && !isInvalid

  def report(vctx: VerificationContext) {
    import vctx.reporter

    status match {
      case VCStatus.Valid =>
        reporter.info(" => VALID")

      case VCStatus.Invalid(cex) =>
        reporter.warning(" => INVALID")
        reporter.warning("Found counter-example:")

        // We use PrettyPrinter explicitly and not ScalaPrinter: printing very
        // large arrays faithfully in ScalaPrinter is hard, while PrettyPrinter
        // is free to simplify
        val strings = cex.toSeq.sortBy(_._1.name).map {
          case (id, v) =>
            (id.asString(vctx), SelfPrettyPrinter.print(v, PrettyPrinter(v))(vctx, vctx.program))
        }

        if (strings.nonEmpty) {
          val max = strings.map(_._1.length).max

          for ((id, v) <- strings) {
            reporter.warning(("  %-"+max+"s -> %s").format(id, v))
          }
        } else {
          reporter.warning(f"  (Empty counter-example)")
        }
      case _ =>
        reporter.warning(" => "+status.name.toUpperCase)
    }
  }
}

object VCResult {
  def unknown = VCResult(VCStatus.Unknown, None, None)
}

sealed abstract class VCStatus(val name: String) {
  override def toString = name
}

object VCStatus {
  case class  Invalid(cex: Model) extends VCStatus("invalid")
  case object Valid extends VCStatus("valid")
  case object Unknown extends VCStatus("unknown")
  case object Timeout extends VCStatus("timeout")
  case object Cancelled extends VCStatus("cancelled")
  case object Crashed extends VCStatus("crashed")
  case object Unsupported extends VCStatus("unsupported")
}
