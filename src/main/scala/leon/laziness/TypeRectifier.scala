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
import HOMemUtil._
import leon.invariant.datastructure.DisjointSets
import invariant.util.ProgramUtil._
import leon.utils.Bijection

/**
 * This performs type parameter inference based on few known facts.
 * This algorithm is inspired by Hindley-Milner type Inference (but not the same).
 * Result is a program in which all type paramters of functions, types of
 * parameters of functions are correct.
 * The subsequent phase performs a local type inference.
 *
 *  We unify the type arguments of `tfd` with type arguments of actual arguments.
 *  Note: we have a cyclic problem here, since we do not know the
 *  type of the variables in the programs, we cannot use them
 *  to infer type parameters, on the other hand we need to know the
 *  type parameters (at least of fundefs) to infer types of variables.
 *  The idea to start from few variables whose types we know are correct
 *  except for type parameters.
 *  Eg. the state parameters, parameters that have closure ADT type (not the '$' type),
 *  some parameters that are not of lazy type ('$') type may also have
 *  correct types, but it is hard to rely on them
 */
class TypeRectifier(p: Program, clFactory: ClosureFactory) {

  val debug = false

  val relfuns = userLevelFunctions(p)
  val memoClasses = clFactory.memoClasses.values.toSet
  val typeClasses = {
    val tc = new DisjointSets[TypeTree]()
    var funInvs = Seq[FunctionInvocation]()
    // go over the body of all funs and compute mappings for place-holder `tparams`
    relfuns.filter(_.hasBody).foreach { fd =>
      postTraversal {
        case fi@FunctionInvocation(TypedFunDef(_, targs), _)
          if targs.exists{ case tp: TypeParameter => isPlaceHolderTParam(tp) case _ => false } =>
            funInvs +:= fi
        case CaseClass(ct: CaseClassType, args) =>
          if (memoClasses(ct.classDef)) { //here, we can trust the types of arguments
            (args zip ct.fieldsTypes) foreach {
              case (arg, ft) =>
                typeInstMap(arg.getType, ft).get.foreach {
                  case (t1, t2) => tc.union(t1, t2)
                }
            }
          }
        case _ =>
      }(fd.fullBody)
    }
    var merged = false
    do {
      merged = false
      funInvs.foreach {
        case fi@FunctionInvocation(TypedFunDef(fd, targs), args) =>
          //println("Considering call: "+ fi+" tparams: "+fd.tparams.mkString(",")+" targs: "+targs)
          // if two fd.tparams are merged, merge the corresponding targs
          val tparams = fd.tparams.map(_.tp)
          val paramToArg = (tparams zip targs).toMap
          //val argToParam = (targs zip tparams).toMap
          tparams.groupBy(tp => tc.findOrCreate(tp)) foreach {
            case (_, eqtparams) => merged ||= tc.union(eqtparams.map(paramToArg))
          }
      }
    } while (merged)
    tc
  }
  val equivTypeParams = typeClasses.toMap
  val fdMap = relfuns.collect {
    case fd if !fd.isLibrary && !fd.isInvariant =>
      val (tempTPs, otherTPs) = fd.tparams.map(_.tp).partition {
        case tp if isPlaceHolderTParam(tp) => true
        case _                             => false
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
            else{
              if(debug)
                println(s"Warning: Cannot find a non-placeholder in equivalence class $tpclass for fundef: \n $fd")
              tpclass.head
            }
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

      case CaseClass(cct, args) =>
        val targs = cct.tps.map {
          case tp: TypeParameter => tpMap.getOrElse(tp, tp)
          case t                 => t
        }.distinct
        CaseClass(CaseClassType(cct.classDef, targs), args map rec)

      case Variable(id) if paramMap.contains(id) =>
        paramMap(id).toVariable
      case TupleSelect(tup, index) =>
        TupleSelect(rec(tup), index)
      case Ensuring(NoTree(_), post) =>
        Ensuring(nfd.fullBody, rec(post)) // the newfd body would already be type correct
      case Operator(args, op) => op(args map rec)
      case t: Terminal        => t
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
        // TODO: what about decreases ?
        //println("New fun: "+fd)
        nfd
      case d => d
    })
  }
}
