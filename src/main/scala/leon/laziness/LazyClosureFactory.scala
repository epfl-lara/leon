package leon
package laziness

import invariant.util._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import LazinessUtil._

//case class ClosureData(tpe: TypeTree, absDef: AbstractClassDef, caseClass: Seq[CaseClassDef])

class LazyClosureFactory(p: Program) {
  val debug = false
  implicit val prog = p

  /**
   * all the operations that could be lazily evaluated
   */
  val lazyopsList = p.definedFunctions.flatMap {
    case fd if (fd.hasBody) =>
      filter(isLazyInvocation)(fd.body.get) map {
        case FunctionInvocation(_, Seq(Lambda(_, FunctionInvocation(tfd, _)))) => tfd.fd
      }
    case _ => Seq()
  }.distinct

  if (debug) {
    println("Lazy operations found: \n" + lazyopsList.map(_.id).mkString("\n"))
  }

  /**
   * Create a mapping from types to the lazy/mem ops that may produce a value of that type
   * TODO: relax the requirement that type parameters of return type of a function
   * lazy evaluated/memoized should include all of its type parameters.
   */
  private def closuresForOps(ops: List[FunDef]) = {
    // using tpe name below to avoid mismatches due to type parameters
    val tpeToLazyops = ops.groupBy(lop => typeNameWOParams(lop.returnType))
    if (debug) {
      println("Type to Ops: " + tpeToLazyops.map {
        case (k, v) => s"$k --> ${v.map(_.id).mkString(",")}"
      }.mkString("\n"))
    }
    val tpeToAbsClass = tpeToLazyops.map {
      case (tpename, ops) =>
        val tpcount = getTypeParameters(ops(0).returnType).size
        //Safety check:
        // (a) check that tparams of all ops should match and should be equal to the tparams of return type
        // (b) all are either memoized or all are lazy
        ops.foreach { op =>
          if (op.tparams.size != tpcount)
            throw new IllegalStateException(s"Type parameters of the lazy/memoized operation ${op.id.name}" +
              "should match the type parameters of the return type of the operation")
        }
        if(ops.size >= 2) {
          ops.tail.forall(op => isMemoized(op) == isMemoized(ops.head))
        }
        val absTParams = (1 to tpcount).map(i => TypeParameterDef(TypeParameter.fresh("T" + i)))
        tpename -> new AbstractClassDef(FreshIdentifier(typeNameToADTName(tpename), Untyped),
          absTParams, None)
    }.toMap
    var opToAdt = Map[FunDef, CaseClassDef]()
    val tpeToADT = tpeToLazyops map {
      case (tpename, ops) =>
        val ismem = isMemoized(ops(0))
        val baseT = ops(0).returnType //TODO: replace targs here i.e, use clresType ?
        val absClass = tpeToAbsClass(tpename)
        val absTParamsDef = absClass.tparams
        val absTParams = absTParamsDef.map(_.tp)

        // create a case class for every operation
        val cdefs = ops map { opfd =>
          assert(opfd.tparams.size == absTParamsDef.size)
          val absType = AbstractClassType(absClass, opfd.tparams.map(_.tp))
          val classid = FreshIdentifier(opNameToCCName(opfd.id.name), Untyped)
          val cdef = new CaseClassDef(classid, opfd.tparams, Some(absType), isCaseObject = false)
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
          if (!ismem) {
            // add a result field as well
            val resField = ValDef(FreshIdentifier("clres", opfd.returnType))
            cdef.setFields(nfields :+ resField)
          } else
            cdef.setFields(nfields)
          absClass.registerChild(cdef)
          opToAdt += (opfd -> cdef)
          cdef
        }
        if (!ismem) {
          // create a case class to represent eager evaluation (when handling lazy ops)
          val clresType = ops.head.returnType match {
            case NAryType(tparams, tcons) => tcons(absTParams)
          }
          val eagerid = FreshIdentifier("Eager" + TypeUtil.typeNameWOParams(clresType))
          val eagerClosure = new CaseClassDef(eagerid, absTParamsDef,
            Some(AbstractClassType(absClass, absTParams)), isCaseObject = false)
          eagerClosure.setFields(Seq(ValDef(FreshIdentifier("a", clresType))))
          absClass.registerChild(eagerClosure)
          (tpename -> (baseT, absClass, cdefs, Some(eagerClosure), ismem))
        } else
          (tpename -> (baseT, absClass, cdefs, None, ismem))
    }
    /*tpeToADT.foreach {
      case (k, v) => println(s"$k --> ${ (v._2 +: v._3).mkString("\n\t") }")
    }*/
    (tpeToADT, opToAdt)
  }

  private val (tpeToADT, opToCaseClass) = closuresForOps(lazyopsList)

  // this fixes an ordering on lazy types
  val lazyTypeNames = tpeToADT.keys.toSeq
  val lazyops = opToCaseClass.keySet
  lazy val caseClassToOp = opToCaseClass map { case (k, v) => v -> k }
  val allClosuresAndParents: Seq[ClassDef] = tpeToADT.values.flatMap(v => (v._2 +: v._3) ++ v._4.toList).toSeq
  val allClosureSet = allClosuresAndParents.toSet

  // lazy operations
  def lazyType(tn: String) = tpeToADT(tn)._1
  def isMemType(tn: String) = tpeToADT(tn)._5
  def absClosureType(tn: String) = tpeToADT(tn)._2
  def closures(tn: String) = tpeToADT(tn)._3
  def eagerClosure(tn: String) = tpeToADT(tn)._4
  def lazyopOfClosure(cl: CaseClassDef) = caseClassToOp(cl)
  def closureOfLazyOp(op: FunDef) = opToCaseClass(op)
  def isLazyOp(op: FunDef) = opToCaseClass.contains(op)
  def isClosureType(cd: ClassDef) = allClosureSet.contains(cd)

  /**
   * Here, the lazy type name is recovered from the closure's name.
   * This avoids the use of additional maps.
   */
  def lazyTypeNameOfClosure(cl: CaseClassDef) = adtNameToTypeName(cl.parent.get.classDef.id.name)

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
      val nparams = (start to i).map(index => TypeParameter.fresh("T" + index))
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
    val ccd = new CaseClassDef(FreshIdentifier("State@"), tparams map TypeParameterDef, None, false)
    ccd.setFields(fields)
    ccd
  }

  def selectFieldOfState(tn: String, st: Expr, stType: CaseClassType) = {
    val selName = typeToFieldName(tn)
    stType.classDef.fields.find { fld => fld.id.name == selName } match {
      case Some(fld) =>
        CaseClassSelector(stType, st, fld.id)
      case _ =>
        throw new IllegalStateException(s"Cannot find a field of $stType with name: $selName")
    }
  }

  val stateUpdateFuns: Map[String, FunDef] =
    lazyTypeNames.map { tn =>
      val fldname = typeToFieldName(tn)
      val tparams = state.tparams.map(_.tp)
      val stType = CaseClassType(state, tparams)
      val param1 = FreshIdentifier("st@", stType)
      val SetType(baseT) = stType.classDef.fields.find { fld => fld.id.name == fldname }.get.getType
      val param2 = FreshIdentifier("cl", baseT)

      val updateFun = new FunDef(FreshIdentifier("updState" + tn),
        state.tparams, Seq(ValDef(param1), ValDef(param2)), stType)
      // create a body for the updateFun:
      val nargs = state.fields.map { fld =>
        val fldSelect = CaseClassSelector(stType, param1.toVariable, fld.id)
        if (fld.id.name == fldname) {
          SetUnion(fldSelect, FiniteSet(Set(param2.toVariable), baseT)) // st@.tn + Set(param2)
        } else {
          fldSelect
        }
      }
      val nst = CaseClass(stType, nargs)
      updateFun.body = Some(nst)
      // Inlining this seems to slow down verification. Why!!
      //updateFun.addFlag(IsInlined)
      (tn -> updateFun)
    }.toMap
}
