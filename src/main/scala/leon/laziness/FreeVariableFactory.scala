package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.TransformationPhase
import LazinessUtil._
import invariant.util.ProgramUtil._

/**
 * A class that maintains a data type that can used to
 * create free variables at different points in the program.
 * All free variables are of type `FreeVar` which can be mapped
 * to a required type by applying uninterpreted functions.
 */
object FreeVariableFactory {

  val fvClass = AbstractClassDef(FreshIdentifier("FreeVar@"), Seq(), None)
  val fvType = AbstractClassType(fvClass, Seq())
  val varCase = {
    val cdef = CaseClassDef(FreshIdentifier("Var@"), Seq(), Some(fvType), false)
    cdef.setFields(Seq(ValDef(FreshIdentifier("fl", fvType))))
    fvClass.registerChild(cdef)
    cdef
  }
  val nextCase = {
    val cdef = CaseClassDef(FreshIdentifier("NextVar@"), Seq(), Some(fvType), false)
    cdef.setFields(Seq(ValDef(FreshIdentifier("fl", fvType))))
    fvClass.registerChild(cdef)
    cdef
  }
  val nilCase = {
    val cdef = CaseClassDef(FreshIdentifier("NilVar@"), Seq(), Some(fvType), false)
    fvClass.registerChild(cdef)
    cdef
  }

  class FreeVarListIterator(initRef: Variable) {
    require(initRef.getType == fvType)
    var refExpr : Expr = initRef
    def current = CaseClass(varCase.typed, Seq(refExpr)) // Var(refExpr)
    def next {
      refExpr = CaseClass(nextCase.typed, Seq(refExpr)) // Next(refExpr)
    }
    // returns the current expressions and increments state
    def nextExpr = {
      val e = current
      next
      e
    }
  }

  def getFreeListIterator(initRef: Variable) = new FreeVarListIterator(initRef)

  var uifuns = Map[TypeTree, FunDef]()
  def getOrCreateUF(t: TypeTree) = {
    uifuns.getOrElse(t, {
      val funName = "uop@" + TypeUtil.typeNameWOParams(t)
      val param = ValDef(FreshIdentifier("a", fvType))
      val tparams = TypeUtil.getTypeParameters(t) map TypeParameterDef.apply _
      val uop = new FunDef(FreshIdentifier(funName), tparams, Seq(param), t)
      uifuns += (t -> uop)
      uop
    })
  }

  class FreeVariableGenerator(initRef: Variable) {
    val flIter = new FreeVarListIterator(initRef)

    /**
     * Free operations are not guaranteed to be unique: They are
     * uninterpreted functions of the form: f(ref).
     * f(res_1) could be equal to f(res_2).
     */
    def nextFV(t: TypeTree) = {
      val uop = getOrCreateUF(t)
      val fv = FunctionInvocation(TypedFunDef(uop, Seq()), Seq(flIter.current))
      flIter.next
      fv
    }

    /**
     * References are guaranteed to be unique.
     */
    def nextRef = {
      val ref = flIter.current
      flIter.next
      ref
    }
  }

  def getFreeVarGenerator(initRef: Variable) = new FreeVariableGenerator(initRef)

  def fvClasses = Seq(fvClass, varCase, nextCase, nilCase)

  def fvFunctions = uifuns.keys.toSeq
}
