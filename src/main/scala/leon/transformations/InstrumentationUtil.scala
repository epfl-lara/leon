/* Copyright 2009-2016 EPFL, Lausanne */

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
  def isInstCall(e: Expr): Boolean = {
    e match {
      case FunctionInvocation(TypedFunDef(fd, _), args) if args.size <= 1 =>
        fd.id.name == name && fd.annotations("library") 
      case _ => false
    }
  }
  def instTarget(e: Expr): Option[Expr] = {
    if (isInstCall(e)) {
      e match {
        case FunctionInvocation(_, Seq()) => None
        case FunctionInvocation(_, Seq(arg)) => Some(arg)
      }      
    } else throw new IllegalStateException("Not inst call: " + e)
  }
  override def toString = name
}

object Time extends Instrumentation {
  override val getType = IntegerType
  override val name = "steps"
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

object Alloc extends Instrumentation {
  override val getType = IntegerType
  override val name = "alloc"
}
//add more instrumentation variables

object InstUtil {

  val InstTypes = Seq(Time, Depth, Rec, TPR, Stack, Alloc)

  val maxFun = {
    val xid = FreshIdentifier("x", IntegerType)
    val yid = FreshIdentifier("y", IntegerType)
    val varx = xid.toVariable
    val vary = yid.toVariable
    val args = Seq(xid, yid)
    val maxType = FunctionType(Seq(IntegerType, IntegerType), IntegerType)
    val mfd = new FunDef(FreshIdentifier("max", maxType, false), Seq(), args.map(arg => ValDef(arg)), IntegerType)

    val cond = GreaterEquals(varx, vary)
    mfd.body = Some(IfExpr(cond, varx, vary))
    mfd.addFlag(Annotation("theoryop", Seq()))
    mfd
  }
  
  def instCall(e: Expr) = InstTypes.find(_.isInstCall(e))

  def getInstSuffixes(fd: FunDef) = {
    val splits = fd.id.name.split("-")
    if (!splits.isEmpty) {
      val instNames = InstTypes.map(_.name).toSet
      splits.tail.dropWhile(x => !instNames.contains(x)).toSeq
    } else Seq[String]()
  }

  def userFunctionName(fd: FunDef) = {
    val splits = fd.id.name.split("-")
    if(!splits.isEmpty) {
      val instNames = InstTypes.map(_.name).toSet
      val suffix = splits.tail.takeWhile(x => !instNames.contains(x)).mkString("-")
      if(suffix.isEmpty()) splits.head
      else splits.head + "-" + suffix        
    } else ""
  }

  def getInstMap(fd: FunDef) = {
    val resvar = getResId(fd).get.toVariable // note: every instrumented function has a postcondition
    val insts = getInstSuffixes(fd) // fd.id.name.split("-").tail // split the name of the function w.r.t '-'
    (insts.zipWithIndex).foldLeft(Map[Expr, String]()) {
      case (acc, (instName, i)) =>
        acc + (TupleSelect(resvar, i + 2) -> instName)
    }
  }

  def getInstExpr(fd: FunDef, inst: Instrumentation) = {
    val resvar = getResId(fd).get.toVariable // note: every instrumented function has a postcondition
    val insts = getInstSuffixes(fd) // split the name of the function w.r.t '-'
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

  def isInstrumented(fd: FunDef) = {
    val comps = fd.id.name.split("-")
    InstTypes.exists { x => comps.contains(x.toString) }
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

  /**
   * Checks if the given expression is a resource bound of the given function.
   */
  def isResourceBoundOf(fd: FunDef)(e: Expr) = {
    val instExprs = InstTypes.map(getInstExpr(fd, _)).collect {
      case Some(inste) => inste
    }.toSet
    !instExprs.isEmpty && isArithmeticRelation(e).get &&
      exists {
        case sub: TupleSelect => instExprs(sub)
        case _                => false
      }(e)
  }
}
