package leon
package laziness

import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.ProgramUtil._
import leon.invariant.util.PredicateUtil._
import HOMemUtil._

/**
 * Generate lemmas that ensure that preconditions hold for closures.
 * Note: here we cannot use `ClosureFactory` for anything other than state,
 * since we work with the translated, type correct program here.
 */
class ClosurePreAsserter(p: Program, clFactory: ClosureFactory) {

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
    lookupOp(cc.ct.classDef).hasPrecondition
  }

  def closureToLambda(cct: CaseClassType) = {
    val newTarget = lookupOp(cct.classDef) //find the target corresponding to the closure
    clFactory.lambdaOfClosure(cct.classDef).get match {
      case Lambda(args, FunctionInvocation(_, allargs)) =>
        val argIndices = args.map(_.id).zipWithIndex.toMap
        // mapping from argIndex to the index at which it is used
        val useToArg = allargs.zipWithIndex.collect {
          case (Variable(id), i) if argIndices.contains(id) => (i -> argIndices(id))
        }.toMap
        // construct a new lambda
        val newparams = newTarget.params.map(_.id).zipWithIndex
        val argTypes = Array.fill[TypeTree](args.size)(Untyped)
        newparams.foreach {
          case (p, i) if useToArg.contains(i) => argTypes(useToArg(i)) = p.getType
          case _                              =>
        }
        val newargs = argTypes.map { FreshIdentifier("arg", _) }
        val newAllArgs = newparams.map {
          case (p, i) if useToArg.contains(i) => newargs(useToArg(i)).toVariable
          case (p, _)                         => p.toVariable
        }
        Lambda(newargs.map(ValDef), FunctionInvocation(TypedFunDef(newTarget, cct.tps), newAllArgs))
    }
  }

  val closuresToPrePath = ProgramUtil.userLevelFunctions(p).flatMap {
    case fd if fd.hasBody =>
      //println("collection closure creation preconditions for: "+fd)
      val closures = CollectorWithPaths {
        case FunctionInvocation(TypedFunDef(fund, _),
          Seq(cc: CaseClass, st)) if isClosureCons(fund) && hasClassInvariants(cc) =>
          (cc, st)
      } traverse (fd.body.get) // Note: closures cannot be created in specs
      closures.map {
        case ((cc@CaseClass(cct: CaseClassType, ccArgs), st), path) =>
          //println(s"Path for $cc : $path")
          //println(s"Path clause : ${path.toPath}")
          anchorfd = Some(fd)
          val l@Lambda(largs, FunctionInvocation(TypedFunDef(target, _), allargs)) = closureToLambda(cct)
          val args = ccArgs  // TODO: return value handling: argsRet.dropRight(1) // drop the return value which is the right-most field
          val nargs =
            if (target.params.size > args.size) // target takes state ?
              args :+ st
            else args
          val stparams =
            if (target.params.size > args.size) // target takes state ?
              Seq(target.paramIds.last)
            else Seq()
          // here, we rely on the order of the captured variables
          val capturedPre = replaceFromIDs(((capturedVars(l) ++ stparams) zip nargs).toMap, capturedPreconditions(l))
          cc -> (capturedPre, path, fd)
      }
    case _ => Seq()
  }.toMap

  // TODO: A nasty way of finding anchor functions
  // Fix this soon !!
  var anchorfd: Option[FunDef] = None
  val lemmas = closuresToPrePath map {
    case (cc, (capturedPre, path, fd)) =>
      anchorfd = Some(fd)      
      val vc = Implies(And(precOrTrue(fd), path.toPath), capturedPre)
      // create a function for each vc
      val lemmaid = FreshIdentifier(cc.ct.classDef.id.name + fd.id.name + "Pre", Untyped, true)
      val params = variablesOf(vc).toSeq.map(v => ValDef(v))
      val tparams = params.flatMap(p => getTypeParameters(p.getType)).distinct map TypeParameterDef
      val lemmafd = new FunDef(lemmaid, tparams, params, BooleanType)
      // reset the types of locals
      val initGamma = params.map(vd => vd.id -> vd.getType).toMap
      lemmafd.body = Some(TypeChecker.inferTypesOfLocals(vc, initGamma))
      val resid = FreshIdentifier("holds", BooleanType)
      lemmafd.postcondition = Some(Lambda(Seq(ValDef(resid)), resid.toVariable))
      //println("Created lemma function: "+lemmafd)
      lemmafd
  }

  /**
   * Create functions that check the monotonicity of the preconditions
   * of the ops
   */
  val monoLemmas = {
    var exprsProcessed = Set[ExprStructure]()
    closuresToPrePath.flatMap {
      case (cc, (capturedPre, _, fd)) =>
        // get the state param
        variablesOf(capturedPre).find(isStateParam) match {
          case Some(stparam) =>
            // remove conjuncts that do not depend on the state
            val preConjs = capturedPre match {
              case And(args) =>
                args.filter(a => variablesOf(a).contains(stparam))
              case l: Let => // checks if the body of the let can be deconstructed as And
                val (letsCons, letsBody) = letStarUnapplyWithSimplify(l)
                letsBody match {
                  case And(args) =>
                    args.filter(a => variablesOf(a).contains(stparam)).map { e => letsCons(e) }
                  case _ => Seq()
                }
              case e => Seq()
            }
            if (preConjs.nonEmpty) {
              val superSt = FreshIdentifier("st2@", stparam.getType)
              val subsetExpr = SubsetOf(stparam.toVariable, superSt.toVariable)
              // create a function for each pre-conjunct that is not processed
              preConjs.map(new ExprStructure(_)).collect {
                case preStruct if !exprsProcessed(preStruct) =>
                  exprsProcessed += preStruct
                  val pred = preStruct.e
                  val vc = Implies(And(subsetExpr, pred),
                    replaceFromIDs(Map(stparam -> superSt.toVariable), pred))
                  val lemmaid = FreshIdentifier(cc.ct.id.name + "PreMonotone", Untyped, true)
                  val params = variablesOf(vc).toSeq.map(v => ValDef(v))
                  val tparams = params.flatMap(p => getTypeParameters(p.getType)).distinct map TypeParameterDef
                  val lemmafd = new FunDef(lemmaid, tparams, params, BooleanType)
                  lemmafd.body = Some(vc)
                  val resid = FreshIdentifier("holds", BooleanType)
                  lemmafd.postcondition = Some(Lambda(Seq(ValDef(resid)), resid.toVariable))
                  lemmafd.addFlag(new Annotation("traceInduct", Seq())) // add the trace induct annotation
                  //println("Created lemma function: "+lemmafd)
                  lemmafd
              }
            } else Seq.empty[FunDef] // nothing to be done
          case None =>
            Seq.empty[FunDef] // nothing to be done
        }
    }
  }

  def apply: Program = {
    if (!lemmas.isEmpty)
      addFunDefs(p, lemmas ++ monoLemmas, anchorfd.get)
    else p
  }
}
