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
import leon.invariant.datastructure.DisjointSets

/**
 * This performs a little bit of Hindley-Milner type Inference
 * to correct the local types and also unify type parameters
 * @param placeHolderParameter Expected to returns true iff a type parameter 
 * 														is meant as a placeholder and cannot be used
 * 														to represent a unified type
 */
class TypeRectifier(p: Program, placeHolderParameter: TypeParameter => Boolean) {

  val typeClasses = {
    var tc = new DisjointSets[TypeTree]()
    p.definedFunctions.foreach {
      case fd if fd.hasBody && !fd.isLibrary =>
        postTraversal {
          case call @ FunctionInvocation(TypedFunDef(fd, tparams), args) =>
            // unify formal type parameters with actual type arguments
            (fd.tparams zip tparams).foreach(x => tc.union(x._1.tp, x._2))
            // unify the type parameters of types of formal parameters with
            // type arguments of actual arguments
            (fd.params zip args).foreach { x =>
              (x._1.getType, x._2.getType) match {
                case (SetType(tf: ClassType), SetType(ta: ClassType)) =>
                  (tf.tps zip ta.tps).foreach { x => tc.union(x._1, x._2) }
                case (tf: TypeParameter, ta: TypeParameter) =>
                  tc.union(tf, ta)
                case (t1, t2) =>
                  // others could be ignored for now as they are not part of the state
                  //TODO: handle this case
                  ;
                /*throw new IllegalStateException(s"Types of formal and actual parameters: ($tf, $ta)"
                    + s"do not match for call: $call")*/
              }
            }
          case _ => ;
        }(fd.fullBody)
      case _ => ;
    }
    tc
  }

  val equivTypeParams = typeClasses.toMap
  
  val fdMap = p.definedFunctions.collect {
    case fd if !fd.isLibrary =>
      val (tempTPs, otherTPs) = fd.tparams.map(_.tp).partition {
        case tp if placeHolderParameter(tp) => true
        case _                              => false
      }
      val others = otherTPs.toSet[TypeTree]
      // for each of the type parameter pick one representative from its equvialence class
      val tpMap = fd.tparams.map {
        case TypeParameterDef(tp) =>
          val tpclass = equivTypeParams.getOrElse(tp, Set(tp))
          val candReps = tpclass.filter(r => others.contains(r) || !r.isInstanceOf[TypeParameter])
          val concRep = candReps.find(!_.isInstanceOf[TypeParameter])
          val rep =
            if (concRep.isDefined) // there exists a concrete type ?
              concRep.get
            else if (!candReps.isEmpty)
              candReps.head
            else
              throw new IllegalStateException(s"Cannot find a non-placeholder in equivalence class $tpclass for fundef: \n $fd")
          tp -> rep
      }.toMap
      val instf = instantiateTypeParameters(tpMap) _
      val paramMap = fd.params.map {
        case vd @ ValDef(id, _) =>
          (id -> FreshIdentifier(id.name, instf(vd.getType)))
      }.toMap
      val ntparams = tpMap.values.toSeq.distinct.collect { case tp: TypeParameter => tp } map TypeParameterDef
      val nfd = new FunDef(fd.id.freshen, ntparams, instf(fd.returnType),
        fd.params.map(vd => ValDef(paramMap(vd.id))))
      fd -> (nfd, tpMap, paramMap)
  }.toMap

  /**
   * Replace fundefs and unify type parameters in function invocations.
   * Replace old parameters by new parameters
   */
  def transformFunBody(ifd: FunDef) = {
    val (nfd, tpMap, paramMap) = fdMap(ifd)
    // need to handle tuple select specially as it breaks if the type of
    // the tupleExpr if it is not TupleTyped.
    // cannot use simplePostTransform because of this
    def rec(e: Expr): Expr = e match {
      case FunctionInvocation(TypedFunDef(callee, targsOld), args) =>
        val targs = targsOld.map {
          case tp: TypeParameter => tpMap.getOrElse(tp, tp)
          case t                 => t
        }.distinct
        val ncallee =
          if (fdMap.contains(callee))
            fdMap(callee)._1
          else callee
        FunctionInvocation(TypedFunDef(ncallee, targs), args map rec)
      case Variable(id) if paramMap.contains(id) =>
        paramMap(id).toVariable
      case TupleSelect(tup, index) => TupleSelect(rec(tup), index)
      case Operator(args, op)      => op(args map rec)
      case t: Terminal             => t
    }
    val nbody = rec(ifd.fullBody)
    //println("Inferring types for: "+ifd.id)
    val initGamma = nfd.params.map(vd => vd.id -> vd.getType).toMap
    TypeChecker.inferTypesOfLocals(nbody, initGamma)
  }

  def apply: Program = {
    copyProgram(p, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if fdMap.contains(fd) =>
        val nfd = fdMap(fd)._1
        if (!fd.fullBody.isInstanceOf[NoTree]) {
          nfd.fullBody = simplifyLetsAndLetsWithTuples(transformFunBody(fd))
        }
        fd.flags.foreach(nfd.addFlag(_))
        //println("New fun: "+fd)
        nfd
      case d => d
    })
  }
}

