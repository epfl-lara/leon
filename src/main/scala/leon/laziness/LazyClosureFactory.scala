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
import purescala.TypeOps._
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

//case class ClosureData(tpe: TypeTree, absDef: AbstractClassDef, caseClass: Seq[CaseClassDef])

class LazyClosureFactory(p: Program) {
  val debug = false
  implicit val prog = p
  /**
   * Create a mapping from types to the lazyops that may produce a value of that type
   * TODO: relax that requirement that type parameters of return type of a function
   * lazy evaluated should include all of its type parameters
   */
  private val (tpeToADT, opToCaseClass) = {
    // collect all the operations that could be lazily evaluated.
    val lazyops = p.definedFunctions.flatMap {
      case fd if (fd.hasBody) =>
        filter(isLazyInvocation)(fd.body.get) map {
          case FunctionInvocation(_, Seq(FunctionInvocation(tfd, _))) => tfd.fd
        }
      case _ => Seq()
    }.distinct
    if (debug) {
      println("Lazy operations found: \n" + lazyops.map(_.id).mkString("\n"))
    }
    // using tpe name below to avoid mismatches due to type parameters
    val tpeToLazyops = lazyops.groupBy(lops => typeNameWOParams(lops.returnType))
    if(debug) {
      println("Type to lazy ops: "+tpeToLazyops.map{
        case (k,v) => s"$k --> ${v.map(_.id).mkString(",")}" }.mkString("\n"))
    }
    val tpeToAbsClass = tpeToLazyops.map {
      case (tpename, ops) =>
        val tpcount = getTypeParameters(ops(0).returnType).size
        // check that tparams of all ops should match and should be equal to the tparams of return type
        // a safety check
        ops.foreach { op =>
          if (op.tparams.size != tpcount)
            throw new IllegalStateException(s"Type parameters of the lazy operation ${op.id.name}" +
              "should match the type parameters of the return type of the operation")
        }
        val absTParams = (1 to tpcount).map(i => TypeParameterDef(TypeParameter.fresh("T" + i)))
        tpename -> AbstractClassDef(FreshIdentifier(typeNameToADTName(tpename), Untyped),
          absTParams, None)
    }.toMap
    var opToAdt = Map[FunDef, CaseClassDef]()
    val tpeToADT = tpeToLazyops map {
      case (tpename, ops) =>
        val baseT = ops(0).returnType //TODO: replace targs here i.e, use clresType ?
        val absClass = tpeToAbsClass(tpename)
        val absTParamsDef = absClass.tparams
        val absTParams = absTParamsDef.map(_.tp)

        // create a case class for every operation
        val cdefs = ops map { opfd =>
          assert(opfd.tparams.size == absTParamsDef.size)
          val absType = AbstractClassType(absClass, opfd.tparams.map(_.tp))
          val classid = FreshIdentifier(opNameToCCName(opfd.id.name), Untyped)
          val cdef = CaseClassDef(classid, opfd.tparams, Some(absType), isCaseObject = false)
          val nfields = opfd.params.map { vd =>
            val fldType = vd.getType
            unwrapLazyType(fldType) match {
              case None =>
                ValDef(FreshIdentifier(vd.id.name, fldType))
              case Some(btype) =>
                val btname = typeNameWOParams(btype)
                val baseAbs = tpeToAbsClass(btname)
                ValDef(FreshIdentifier(vd.id.name,
                    AbstractClassType(baseAbs, getTypeParameters(btype))))
            }
          }
          // add a result field as well
          val resField = ValDef(FreshIdentifier("clres", opfd.returnType))
          cdef.setFields(nfields :+ resField)
          absClass.registerChild(cdef)
          opToAdt += (opfd -> cdef)
          cdef
        }
        // create a case class to represent eager evaluation
        val clresType = ops(0).returnType match {
          case NAryType(tparams, tcons) => tcons(absTParams)
        }
        val eagerid = FreshIdentifier("Eager"+TypeUtil.typeNameWOParams(clresType))
        val eagerClosure = CaseClassDef(eagerid, absTParamsDef,
            Some(AbstractClassType(absClass, absTParams)), isCaseObject = false)
        eagerClosure.setFields(Seq(ValDef(FreshIdentifier("a", clresType))))
        absClass.registerChild(eagerClosure)
        (tpename -> (baseT, absClass, cdefs, eagerClosure))
    }
    /*tpeToADT.foreach {
      case (k, v) => println(s"$k --> ${ (v._2 +: v._3).mkString("\n\t") }")
    }*/
    (tpeToADT, opToAdt)
  }

  // this fixes an ordering on lazy types
  val lazyTypeNames = tpeToADT.keys.toSeq

  val lazyops = opToCaseClass.keySet

  val allClosuresAndParents : Seq[ClassDef] = tpeToADT.values.flatMap(v => v._2 +: v._3 :+ v._4).toSeq

  val allClosureSet = allClosuresAndParents.toSet

  def lazyType(tn: String) = tpeToADT(tn)._1

  def absClosureType(tn: String) = tpeToADT(tn)._2

  def closures(tn: String) = tpeToADT(tn)._3

  def eagerClosure(tn: String) = tpeToADT(tn)._4

  lazy val caseClassToOp = opToCaseClass map { case (k, v) => v -> k }

  def lazyopOfClosure(cl: CaseClassDef) = caseClassToOp(cl)

  def closureOfLazyOp(op: FunDef) = opToCaseClass(op)

  def isLazyOp(op: FunDef) = opToCaseClass.contains(op)

  def isClosureType(cd: ClassDef) = allClosureSet.contains(cd)

  /**
   * Here, the lazy type name is recovered from the closure's name.
   * This avoids the use of additional maps.
   */
  def lazyTypeNameOfClosure(cl: CaseClassDef) =  adtNameToTypeName(cl.parent.get.classDef.id.name)

  /**
   * Define a state as an ADT whose fields are sets of closures.
   * Note that we need to ensure that there are state ADT is not recursive.
   */
  val state = {
    var tparams = Seq[TypeParameter]()
    var i = 0
    def freshTParams(n: Int): Seq[TypeParameter] = {
      val start = i + 1
      i += n // create 'n' fresh ids
      val nparams = (start to i).map(index => TypeParameter.fresh("T"+index))
      tparams ++= nparams
      nparams
    }
    // field of the ADT
    val fields = lazyTypeNames map { tn =>
      val absClass = absClosureType(tn)
      val tparams = freshTParams(absClass.tparams.size)
      val fldType = SetType(AbstractClassType(absClass, tparams))
      ValDef(FreshIdentifier(typeToFieldName(tn), fldType))
    }
    val ccd = CaseClassDef(FreshIdentifier("State@"), tparams map TypeParameterDef, None, false)
    ccd.setFields(fields)
    ccd
  }

  def selectFieldOfState(tn: String, st: Expr, stType: CaseClassType) = {
    val selName = typeToFieldName(tn)
    stType.classDef.fields.find{ fld => fld.id.name ==  selName} match {
      case Some(fld) =>
        CaseClassSelector(stType, st, fld.id)
      case _ =>
        throw new IllegalStateException(s"Cannot find a field of $stType with name: $selName")
    }
  }

  val stateUpdateFuns : Map[String, FunDef] =
    lazyTypeNames.map{ tn =>
      val fldname = typeToFieldName(tn)
      val tparams = state.tparams.map(_.tp)
      val stType = CaseClassType(state, tparams)
      val param1 = FreshIdentifier("st@", stType)
      val SetType(baseT) = stType.classDef.fields.find{ fld => fld.id.name == fldname}.get.getType
      val param2 = FreshIdentifier("cl", baseT)

      // TODO: as an optimization we can mark all these functions as inline and inline them at their callees
      val updateFun = new FunDef(FreshIdentifier("updState"+tn),
          state.tparams, Seq(ValDef(param1), ValDef(param2)), stType)
      // create a body for the updateFun:
      val nargs = state.fields.map{ fld =>
        val fldSelect = CaseClassSelector(stType, param1.toVariable, fld.id)
        if(fld.id.name == fldname) {
          SetUnion(fldSelect, FiniteSet(Set(param2.toVariable), baseT)) // st@.tn + Set(param2)
        } else {
          fldSelect
        }
      }
      val nst = CaseClass(stType, nargs)
      updateFun.body = Some(nst)
      (tn -> updateFun)
    }.toMap
}
