package leon
package laziness

import invariant.util._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._

/**
 * A class that maintains a data type that can used to
 * create free variables at different points in the program.
 * All free variables are of type `FreeVar` which can be mapped
 * to a required type by applying uninterpreted functions.
 */
object FreeVariableFactory {

  val fvClass = new AbstractClassDef(FreshIdentifier("FreeVar@"), Seq(), None)
  val fvType = AbstractClassType(fvClass, Seq())
  val varCase = {
    val cdef = new CaseClassDef(FreshIdentifier("Var@"), Seq(), Some(fvType), false)
    cdef.setFields(Seq(ValDef(FreshIdentifier("fl", fvType))))
    fvClass.registerChild(cdef)
    cdef
  }
  val nextCase = {
    val cdef = new CaseClassDef(FreshIdentifier("NextVar@"), Seq(), Some(fvType), false)
    cdef.setFields(Seq(ValDef(FreshIdentifier("fl", fvType))))
    fvClass.registerChild(cdef)
    cdef
  }
  val nilCase = {
    val cdef = new CaseClassDef(FreshIdentifier("NilVar@"), Seq(), Some(fvType), false)
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
