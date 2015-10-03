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
import leon.verification.AnalysisPhase
import LazinessUtil._

/**
 * Generate lemmas that ensure that preconditions hold for closures.
 */
class ClosurePreAsserter(p: Program) {

  def hasClassInvariants(cc: CaseClass): Boolean = {
    val opname = ccNameToOpName(cc.ct.classDef.id.name)
    functionByName(opname, p).get.hasPrecondition
  }

  // A nasty way of finding anchor functions
  // Fix this soon !!
  var anchorfd: Option[FunDef] = None
  val lemmas = p.definedFunctions.flatMap {
    case fd if (fd.hasBody && !fd.isLibrary) =>
      //println("collection closure creation preconditions for: "+fd)
      val closures = CollectorWithPaths {
        case FunctionInvocation(TypedFunDef(fund, _),
          Seq(cc: CaseClass, st)) if isClosureCons(fund) && hasClassInvariants(cc) =>
          (cc, st)
      } traverse (fd.body.get) // Note: closures cannot be created in specs
      // Note: once we have separated normal preconditions from state preconditions
      // it suffices to just consider state preconditions here
      closures.map {
        case ((CaseClass(CaseClassType(ccd, _), args), st), path) =>
          anchorfd = Some(fd)
          val target = functionByName(ccNameToOpName(ccd.id.name), p).get //find the target corresponding to the closure
          val pre = target.precondition.get
          val nargs =
            if (target.params.size > args.size) // target takes state ?
              args :+ st
            else args
          val pre2 = replaceFromIDs((target.params.map(_.id) zip nargs).toMap, pre)
          val vc = Implies(And(Util.precOrTrue(fd), path), pre2)
          // create a function for each vc
          val lemmaid = FreshIdentifier(ccd.id.name + fd.id.name + "Lem", Untyped, true)
          val params = variablesOf(vc).toSeq.map(v => ValDef(v))
          val tparams = params.flatMap(p => getTypeParameters(p.getType)).distinct map TypeParameterDef
          val lemmafd = new FunDef(lemmaid, tparams, BooleanType, params)
          // reset the types of locals
          val initGamma = params.map(vd => vd.id -> vd.getType).toMap
          lemmafd.body = Some(TypeChecker.inferTypesOfLocals(vc, initGamma))
          // assert the lemma is true
          val resid = FreshIdentifier("holds", BooleanType)
          lemmafd.postcondition = Some(Lambda(Seq(ValDef(resid)), resid.toVariable))
          //println("Created lemma function: "+lemmafd)
          lemmafd
      }
    case _ => Seq()
  }

  def apply: Program = {
    if (!lemmas.isEmpty)
      addFunDefs(p, lemmas, anchorfd.get)
    else p
  }
}

