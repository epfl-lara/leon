package leon
package laziness

import invariant.structure.FunctionUtils._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import LazinessUtil._
import leon.invariant.datastructure.DisjointSets
import invariant.util.ProgramUtil._

/**
 * This performs type parameter inference based on few known facts.
 * This algorithm is inspired by Hindley-Milner type Inference (but not the same).
 * Result is a program in which all type paramters of functions, types of
 * parameters of functions are correct.
 * The subsequent phase performs a local type inference.
 */
class TypeRectifier(p: Program, clFactory: LazyClosureFactory) {

  val typeClasses = {
    val tc = new DisjointSets[TypeTree]()
    p.definedFunctions.foreach {
      case fd if fd.hasBody && !fd.isLibrary && !fd.isInvariant =>
        postTraversal {
          case call @ FunctionInvocation(TypedFunDef(fd, tparams), args) =>
            // unify formal type parameters with actual type arguments
            (fd.tparams zip tparams).foreach(x => tc.union(x._1.tp, x._2))
            /**
             *  Unify the type parameters of types of formal parameters with
             *  type arguments of actual arguments.
             *  Note: we have a cyclic problem here, since we do not know the
             *  type of the variables in the programs, we cannot use them
             *  to infer type parameters, on the other hand we need to know the
             *  type parameters (at least of fundefs) to infer types of variables.
             *  The idea to start from few variables whose types we know are correct
             *  except for type paramters.
             *  Eg. the state parameters, parameters that have closure ADT type (not the '$' type),
             *  some parameters that are not of lazy type ('$') type may also have
             *  correct types, but it is hard to rely on them
             */
            (fd.params zip args).foreach { x =>
              (x._1.getType, x._2.getType) match {
                case (CaseClassType(cd1, targs1), CaseClassType(cd2, targs2)) if cd1 == cd2 && cd1 == clFactory.state =>
                  (targs1 zip targs2).foreach {
                    case (t1: TypeParameter, t2: TypeParameter) =>
                      tc.union(t1, t2)
                    case _ =>
                  }
                case (ct1: ClassType, ct2: ClassType)
                  if clFactory.isClosureType(ct1.classDef) && clFactory.isClosureType(ct1.classDef) =>
                  // both types are newly created closures, so their types can be trusted
                  (ct1.tps zip ct2.tps).foreach {
                    case (t1: TypeParameter, t2: TypeParameter) =>
                      tc.union(t1, t2)
                    case _ =>
                  }
                case (t1, t2) =>
                /*throw new IllegalStateException(s"Types of formal and actual parameters: ($tf, $ta)"
                    + s"do not match for call: $call")*/
              }
            }
          // consider also set contains methods
          case ElementOfSet(arg, set) =>
            // merge the type parameters of `arg` and `set`
            set.getType match {
              case SetType(baseT) =>
                // TODO: this may break easily. Fix this.
                // Important: here 'arg' may have type lazy type $[ltype]
                // we need to get the type argument of ltype
                getTypeParameters(arg.getType) zip getTypeArguments(baseT) foreach {
                  case (tf, ta) =>
                    tc.union(tf, ta)
                }
              case _ =>
            }
          case _ =>
        }(fd.fullBody)
      case _ => ;
    }
    tc
  }

  val equivTypeParams = typeClasses.toMap

  val fdMap = p.definedFunctions.collect {
    case fd if !fd.isLibrary && !fd.isInvariant =>
      val (tempTPs, otherTPs) = fd.tparams.map(_.tp).partition {
        case tp if isPlaceHolderTParam(tp) => true
        case _ => false
      }
      val others = otherTPs.toSet[TypeTree]
      // for each of the type parameter pick one representative from its equivalence class
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
        case vd @ ValDef(id) =>
          (id -> FreshIdentifier(id.name, instf(vd.getType)))
      }.toMap
      val ntparams = fd.tparams.map(tpd => tpMap(tpd.tp)).distinct.collect {
        case tp: TypeParameter => tp
      } map TypeParameterDef
      val nfd = new FunDef(fd.id.freshen, ntparams, fd.params.map(vd => ValDef(paramMap(vd.id))),
        instf(fd.returnType))
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
      case FunctionInvocation(TypedFunDef(callee, targsOld), args) => // this is already done by the type checker
        val targs = targsOld.map {
          case tp: TypeParameter => tpMap.getOrElse(tp, tp)
          case t => t
        }.distinct
        val ncallee =
          if (fdMap.contains(callee))
            fdMap(callee)._1
          else callee
        FunctionInvocation(TypedFunDef(ncallee, targs), args map rec)

      case CaseClass(cct, args) =>
        val targs = cct.tps.map {
          case tp: TypeParameter => tpMap.getOrElse(tp, tp)
          case t => t
        }.distinct
        CaseClass(CaseClassType(cct.classDef, targs), args map rec)

      case Variable(id) if paramMap.contains(id) =>
        paramMap(id).toVariable
      case TupleSelect(tup, index) =>
        TupleSelect(rec(tup), index)
      case Ensuring(NoTree(_), post) =>
        Ensuring(nfd.fullBody, rec(post)) // the newfd body would already be type correct
      case Operator(args, op) => op(args map rec)
      case t: Terminal => t
    }
    val nbody = rec(ifd.fullBody)
    val initGamma = nfd.params.map(vd => vd.id -> vd.getType).toMap

    //println(s"Inferring types for ${ifd.id}: "+nbody)
    val typedBody = TypeChecker.inferTypesOfLocals(nbody, initGamma)
    /*if(ifd.id.name.contains("pushLeftWrapper")) {
      //println(s"Inferring types for ${ifd.id} new fun: $nfd \n old body: ${ifd.fullBody} \n type correct body: $typedBody")
      System.exit(0)
    }*/
    typedBody
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
