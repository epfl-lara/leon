package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import leon.utils.Library
import invariant.util._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._

sealed abstract class Instrumentation {
  val getType: TypeTree
  val name: String
  def isInstVariable(e: Expr): Boolean = {
    e match {
      case FunctionInvocation(TypedFunDef(fd, _), _) if (fd.id.name == name && fd.annotations("library")) =>
        true
      case _ => false
    }
  }
  override def toString = name
}

object Time extends Instrumentation {
  override val getType = IntegerType
  override val name = "time"
}
object Depth extends Instrumentation {
  override val getType = IntegerType
  override val name = "depth"
}
object Rec extends Instrumentation {
  override val getType = IntegerType
  override val name = "rec"
}

/**
 * time per recursive step.
 */
object TPR extends Instrumentation {
  override val getType = IntegerType
  override val name = "tpr"
}

object Stack extends Instrumentation {
  override val getType = IntegerType
  override val name = "stack"
}
//add more instrumentation variables

object InstUtil {

  val maxFun = {
    val xid = FreshIdentifier("x", IntegerType)
    val yid = FreshIdentifier("y", IntegerType)
    val varx = xid.toVariable
    val vary = yid.toVariable
    val args = Seq(xid, yid)
    val maxType = FunctionType(Seq(IntegerType, IntegerType), IntegerType)
    val mfd = new FunDef(FreshIdentifier("max", maxType, false), Seq(), args.map((arg) => ValDef(arg, Some(arg.getType))), IntegerType)

    val cond = GreaterEquals(varx, vary)
    mfd.body = Some(IfExpr(cond, varx, vary))
    mfd.addFlag(Annotation("theoryop", Seq()))
    mfd
  }

  def userFunctionName(fd: FunDef) = {
    val splits = fd.id.name.split("-")
    if(!splits.isEmpty) splits(0)
    else ""
  }

  def getInstMap(fd: FunDef) = {
    val resvar = getResId(fd).get.toVariable // note: every instrumented function has a postcondition
    val insts = fd.id.name.split("-").tail // split the name of the function w.r.t '-'
    (insts.zipWithIndex).foldLeft(Map[Expr, String]()) {
      case (acc, (instName, i)) =>
        acc + (TupleSelect(resvar, i + 2) -> instName)
    }
  }

  def getInstExpr(fd: FunDef, inst: Instrumentation) = {
    val resvar = getResId(fd).get.toVariable // note: every instrumented function has a postcondition
    val insts = fd.id.name.split("-").tail // split the name of the function w.r.t '-'
    val index = insts.indexOf(inst.name)
    if (index >= 0)
      Some(TupleSelect(resvar, index + 2))
    else None
  }

  def getInstVariableMap(fd: FunDef) = {
    getInstMap(fd).map {
      case (ts, instName) =>
        (ts -> Variable(FreshIdentifier(instName, IntegerType)))
    }
  }

  def isInstrumented(fd: FunDef, instType: Instrumentation) = {
    fd.id.name.split("-").contains(instType.toString)
  }

  def resultExprForInstVariable(fd: FunDef, instType: Instrumentation) = {
    getInstVariableMap(fd).collectFirst {
      case (k, Variable(id)) if (id.name == instType.toString) => k
    }
  }

  def replaceInstruVars(e: Expr, fd: FunDef): Expr = {
    val resvar = getResId(fd).get.toVariable
    val newres = FreshIdentifier(resvar.id.name, resvar.getType).toVariable
    replace(getInstVariableMap(fd) + (TupleSelect(resvar, 1) -> newres), e)
  }
}
