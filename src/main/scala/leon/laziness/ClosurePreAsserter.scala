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
import leon.invariant.util.ProgramUtil._
import leon.invariant.util.PredicateUtil._
import LazinessUtil._

/**
 * Generate lemmas that ensure that preconditions hold for closures.
 * Note: here we cannot use `ClosureFactory` for anything other than state,
 * since we work with the translated, type correct program here.
 */
class ClosurePreAsserter(p: Program) {

  /**
   * A mapping from `closures` that are *created* in the program
   * to the corresponding functions
   */
  var ccToOp = Map[CaseClassDef, FunDef]()
  def lookupOp(ccd: CaseClassDef): FunDef = {
    ccToOp.getOrElse(ccd, {
      val opname = ccNameToOpName(ccd.id.name)
      val op = functionByName(opname, p).get
      ccToOp += (ccd -> op)
      op
    })
  }

  def hasClassInvariants(cc: CaseClass): Boolean = {
    //val opname = ccNameToOpName(cc.ct.classDef.id.name)
    //functionByName(opname, p).get
    lookupOp(cc.ct.classDef).hasPrecondition
  }

  // TODO: A nasty way of finding anchor functions
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
        case ((CaseClass(CaseClassType(ccd, _), argsRet), st), path) =>
          anchorfd = Some(fd)
          val target = lookupOp(ccd) //functionByName(ccNameToOpName(ccd.id.name), p).get //find the target corresponding to the closure
          val pre = target.precondition.get
          val args = argsRet.dropRight(1) // drop the return value which is the right-most field
          val nargs =
            if (target.params.size > args.size) // target takes state ?
              args :+ st
            else args
          val pre2 = replaceFromIDs((target.params.map(_.id) zip nargs).toMap, pre)
          val vc = Implies(And(precOrTrue(fd), path), pre2)
          // create a function for each vc
          val lemmaid = FreshIdentifier(ccd.id.name + fd.id.name + "Lem", Untyped, true)
          val params = variablesOf(vc).toSeq.map(v => ValDef(v))
          val tparams = params.flatMap(p => getTypeParameters(p.getType)).distinct map TypeParameterDef
          val lemmafd = new FunDef(lemmaid, tparams, params, BooleanType)
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

  /**
   * Create functions that check the monotonicity of the preconditions
   * of the ops
   */
  val monoLemmas = {
    ccToOp.values.flatMap {
      case op if op.hasPrecondition =>
        // get the state param
        op.paramIds.find(isStateParam) match {
          case Some(stparam) =>
            // simplify the pre by removing the disjuncts that do not depend on the state
            val pre = op.precondition.get match {
              case And(args) =>
                createAnd(args.filter(a => variablesOf(a).contains(stparam)))
              case l: Let => // checks if the body of the let can be deconstructed as And
                val (letsCons, letsBody) = letStarUnapply(l)
                letsBody match {
                  case And(args) =>
                    letsCons(createAnd(args.filter(a => variablesOf(a).contains(stparam))))
                  case _ => Util.tru
                }
              case e => Util.tru
            }
            if (pre != Util.tru) {
              // create a new state parameter
              val superSt = FreshIdentifier("st2@", stparam.getType)
              val stType = stparam.getType.asInstanceOf[CaseClassType]
              // assert that every component of `st` is a subset of `stparam`
              val subsetExpr = createAnd(
                stType.classDef.fields.map { fld =>
                  val fieldSelect = (id: Identifier) => CaseClassSelector(stType, id.toVariable, fld.id)
                  SubsetOf(fieldSelect(stparam), fieldSelect(superSt))
                })
              val vc = Implies(And(subsetExpr, pre),
                replaceFromIDs(Map(stparam -> superSt.toVariable), pre))
              // create a function for each vc
              val lemmaid = FreshIdentifier(op.id.name + "PreMonotone", Untyped, true)
              val params = variablesOf(vc).toSeq.map(v => ValDef(v))
              val lemmafd = new FunDef(lemmaid, op.tparams, params, BooleanType)
              lemmafd.body = Some(vc)
              // assert that the lemma is true
              val resid = FreshIdentifier("holds", BooleanType)
              lemmafd.postcondition = Some(Lambda(Seq(ValDef(resid)), resid.toVariable))
              // add the trace induct annotation
              lemmafd.addFlag(new Annotation("traceInduct", Seq()))
              //println("Created lemma function: "+lemmafd)
              Seq(lemmafd)
            } else Seq.empty[FunDef] // nothing to be done
          case None =>
            Seq.empty[FunDef] // nothing to be done
        }
      case _ =>
        Seq.empty[FunDef] // nothing to be done
    }
  }

  def apply: Program = {
    if (!lemmas.isEmpty)
      addFunDefs(p, lemmas ++ monoLemmas, anchorfd.get)
    else p
  }
}
