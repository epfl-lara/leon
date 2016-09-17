package leon
package laziness

import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.TypeOps
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import HOMemUtil._
import purescala.Extractors._
import ProgramUtil._

/**
 * TODO: Support type instantiations. Note that currently we cannot have functions/function types in the program,
 * where one is an instantiation of the other.
 * To support it we should specialize the dispatchers foreach instantiation.
 * TODO: Make finiteness an annotation, and add support for automatically verifying it.
 */
class ClosureFactory(p: Program, funsManager: FunctionsManager) {
  val debug = false

  def createAbstractClass(tpename: String, tparamCount: Int): AbstractClassDef = {
    val absTParams = (1 to tparamCount).map(i => TypeParameterDef(TypeParameter.fresh("T" + i)))
    new AbstractClassDef(FreshIdentifier(typeNameToADTName(tpename), Untyped), absTParams, None)
  }

  def createCaseClass(name: String, absClass: AbstractClassDef, fields: Seq[ValDef]): CaseClassDef = {
    val classid = FreshIdentifier(opNameToCCName(name), Untyped)
    val fieldTParams = fields.flatMap{ v => getTypeParameters(v.getType) }.distinct
    val tparams = fieldTParams ++ absClass.tparams.map(_.tp).drop(fieldTParams.size)
    val cdef = new CaseClassDef(classid, tparams map TypeParameterDef, Some(AbstractClassType(absClass, tparams)), isCaseObject = false)
    cdef.setFields(fields)
    absClass.registerChild(cdef)
    cdef
  }

  import funsManager._
  /**
   * Create an abstract class to represent memoized functions
   * Type parameters of the abstract class are a superset of type parameters of all the function
   */
  val memoAbsClass = {
    val tparamSize =
      if(memoFuns.isEmpty) 0
      else memoFuns.map(_.tparams.size).max
    createAbstractClass("MemoFuns", tparamSize)
  }

  /**
   * Checks if two lambda terms are equal modulo alpha renaming and captured variable names
   */
  class CanonLambda(val l: Lambda) {
    val Lambda(argsDefs, FunctionInvocation(TypedFunDef(target, _), params)) = l
    val args = argsDefs.map(_.id)
    val argPos = params.zipWithIndex.collect {
      case (Variable(id), i) if args.contains(id) => (i, args.indexOf(id))
    }

    override def equals(that: Any): Boolean = {
      that match {
        case o: CanonLambda => o.target == target && o.argPos == argPos
        case _              => false
      }
    }
    override def hashCode = args.size ^ (target.hashCode() << 3)
  }

  def lambdaParametersAndTParams(l: Lambda) = {
    val cvars = capturedVars(l)
    val tparams = cvars.flatMap{ v => getTypeParameters(v.getType) }.distinct
    (cvars, tparams)
  }

  val typeAnalysis = new FunctionTypeAnalysis(p, funsManager)
  /**
   * Create a mapping from types to the lambda that may produce a value of that type.
   * TODO: are we handling subtype/supertypes correctly in lambdas List ?
   */
  private def closuresForOps = {
    /**
     * Checks if there are no function types in program where one is an instantiation of another.
     * This is currently not supported.
     */
    funTypesInProgram.groupBy { case FunctionType(argts, _) => argts.size }.foreach {
      case (_, ftypes) =>
        val reps = ftypes.groupBy(canonTypeName).map(_._2.head).toArray.distinct
        //val fta = reps.map(_.getType)
        //println("Distinct types with same number of arguments: "+fta.mkString(","))
        for (i <- 0 until reps.length)
          for (j <- i + 1 until reps.length) {
            if (isTypeInstance(reps(i), reps(j)))
              throw new IllegalStateException(s"${reps(i)} and ${reps(j)} have insantiatiable types, which is not supported as of now!")
          }
    }
    val lambMap = lambdasList.groupBy(lop => canonTypeName(lop.getType)) // using tpe name below to avoid mismatches due to type parameters
    val tpeToLambda = funTypesInProgram.groupBy(canonTypeName).map{
      case (tname, tps) => tname -> (tps.head, lambMap.getOrElse(tname, Seq()))
    }.toMap
    if (debug) {
      println("Type to Lambdas: " + tpeToLambda.map { case (k, (_, v)) => s"$k --> ${v.mkString(",")}" }.mkString("\n"))
    }
    /**
     * Another important requirement: the type parameters of the captured variables
     * need to be subsumed by the type parameters of the function type.
     * Note: Otherwise, there is not much point in the capturing the variable !
     */
    val tpeToAbsClass = tpeToLambda.map {
      case (tpename, (ft, lams)) =>
        val tpcount = getTypeParameters(ft).size
        lams.foreach { l =>
          if(lambdaParametersAndTParams(l)._2.size > tpcount)
            throw new IllegalStateException(s"Type parameters of captured variables of $l are not contained in the type parameters of the type. This is not supported!")
        }
        tpename -> (ft, createAbstractClass(tpename, tpcount))
    }.toMap

    def createFields(args: Seq[Identifier]) = {
      args.map { v =>
        val realType = TypeOps.bestRealType(v.getType)
        ValDef(FreshIdentifier(v.name, replaceClosureTypes(realType, tpeToAbsClass.values.toSeq)))
      }
    }

    var opToAdt = Map[CanonLambda, CaseClassDef]()
    var stateUpdatingTypes = Set[String]()
    var stateNeedingTypes = Set[String]()
    var escapingTypes = Set[String]()
    val tpeToADT = tpeToLambda map { case (tpename, (ft, lambdas)) => // we create a closure for each lambda and a closure to represent an uninterpreted argument
        val absClass = tpeToAbsClass(tpename)._2
        // create a case class for every lambda (but share them if they invoke the same function with same captured vars)
        val canonLambdas = lambdas.map(l => new CanonLambda(l)).distinct
        val cdefs = canonLambdas map (cl => cl.l match {
          case l@Lambda(_, FunctionInvocation(TypedFunDef(target, _), _)) =>
            // build closure for the target
            val fieldIds = capturedVars(l)
            val cdef = createCaseClass(target.id.name + "L", absClass, createFields(fieldIds))
            // TODO: not clear for now how to enforce this ? (We can later on check how this assumption can be enforced. We can make this an assumption.)
            /*if (ismem) { // add a result field as well to the closures
              val resField = ValDef(FreshIdentifier("clres", opfd.returnType))
              cdef.setFields(nfields :+ resField)
            } else */
            opToAdt += (cl -> cdef)
            cdef
        })
        val ucase = if (typeAnalysis.isEscapingType(ft)) {
          //println("Found escaping type: "+ft)
          stateNeedingTypes += tpename
          stateUpdatingTypes += tpename
          escapingTypes += tpename
          val unknownCase = createCaseClass("U" + tpename, absClass, Seq())
          Some(unknownCase)
        } else {
          val targets = canonLambdas.map { _.l.body.asInstanceOf[FunctionInvocation].tfd.fd }
          if (targets.exists(funsNeedStates))
            stateNeedingTypes += tpename
          if (targets.exists(funsRetStates))
            stateUpdatingTypes += tpename
          None
        }
        (tpename -> (ft, absClass, cdefs, ucase))
    }
    // create a case class for each memoized function
    val memoClasses = memoFuns.map { memofun =>
      val fields = createFields(memofun.params.map(_.id))
      val cdef = createCaseClass(memofun.id.name + "M", memoAbsClass, fields) // the suffix 'M' denotes memoized funvals
      (memofun -> cdef)
    }.toMap
    /*tpeToADT.foreach {
      case (k, v) => println(s"$k --> ${ (v._2 +: v._3).mkString("\n\t") }")
    }*/
    (tpeToADT, opToAdt, memoClasses, stateNeedingTypes, stateUpdatingTypes, escapingTypes)
  }

  val (tpeToADT, opToCaseClass, memoClasses, stateNeedingTypes, stateUpdatingTypes, escapingTypes) = closuresForOps
  if(debug)
    println("Escaping types: "+escapingTypes.mkString(",")+"\n")

  val closureTypeNames = tpeToADT.keys.toSeq   // this fixes an ordering on clsoure types
  val canonLambdas = opToCaseClass.keySet
  val allClosuresAndParents: Seq[ClassDef] = tpeToADT.values.flatMap(v => (v._2 +: v._3) ++ v._4.toSeq).toSeq
  val closureNames = allClosuresAndParents.map(_.id.name).toSet
  val memoClosures = {
    val cls = memoClasses.values.toSeq
    if(cls.isEmpty) { // no memoized functin in the program, however there can be  functions coming from outside
      val defMem = createCaseClass("DMem", memoAbsClass, Seq())      
      Seq(memoAbsClass, defMem) // we create a default case just to make things type check
    }
    else memoAbsClass +: cls
  }
  val memoClasesByName = memoClasses.map{ case (k,v) => (v.id.name -> k) }.toMap

  def functionType(tn: String) = tpeToADT(tn)._1
  def absClosure(tn: String) = tpeToADT(tn)._2
  def concreteClosures(tn: String) = tpeToADT(tn)._3
  def unknownClosure(tn: String) = tpeToADT(tn)._4

  def functionTypeToClosure(t: TypeTree) = {
    t match {
      case t: FunctionType =>
        AbstractClassType(absClosure(typeNameWOParams(t)), getTypeParameters(t))
      case _ => t
    }
  }

  val ftnAbs = tpeToADT.values.map{e => (e._1, e._2)}.toSeq
  def absClosureForFunctionType(absTypes: Seq[(TypeTree, AbstractClassDef)], ft: FunctionType) = {
    absTypes.collectFirst{
      case (tpe, absClass) if isTypeInstance(ft, tpe) =>
        (tpe, absClass)
    }
  }

  def uninstantiatedFunctionTypeName(ft: TypeTree) = {
    tpeToADT.collectFirst {
      case (tpename, (tpe, _, _, _)) if isTypeInstance(ft, tpe) =>
        tpename
    }
  }

  /**
   * Do a recursive (pre-order) replacements of types
   */
  def replaceClosureTypes(t: TypeTree, absTypes: Seq[(TypeTree, AbstractClassDef)] = ftnAbs): TypeTree = {
    t match {
      case ft: FunctionType =>
        val rootTypesOpt = absClosureForFunctionType(absTypes, ft)
        rootTypesOpt match {
          case None =>
            throw new IllegalStateException(s"No lambda compatible with type: $t exists in the program")
          case Some((uninstType, absClass)) =>
//            println(s"Getting type arguments of unintstType: $uninstType instType: $ft")
            val ftparams = getTypeArguments(ft, uninstType).get
            // here, we have the guarantee that the `abstractType` wouldn't take any more type parameters than its corresponding function type
            AbstractClassType(absClass, ftparams)
        }
      case NAryType(tps, tcons) =>
        tcons(tps.map(replaceClosureTypes(_, absTypes)))
    }
  }

  /**
   * Given a closure computes a lambda for the closure by invoking the target function
   */
  val caseClassToOp = opToCaseClass map { case (k, v) => v -> k }
      
  def lambdaOfClosure(cl: CaseClassDef) = caseClassToOp.get(cl).map(_.l)
  def targetOfClosure(cl: CaseClassDef) = caseClassToOp.get(cl) match {
    case Some(canonl) =>
      val Lambda(_, FunctionInvocation(tfd, _)) = canonl.l
      Some(tfd.fd)
    case _ => None
  }
  
  def lambdaOfClosureByName(clname: String): Option[Lambda] =
    caseClassToOp.find(_._1.id.name == clname).map(_._2.l)

  /**
   * Computes a closure for a lambda application
   */
  def closureOfLambda(l: Lambda) = opToCaseClass(new CanonLambda(l))
  def isClosureType(cd: ClassDef) = allClosuresAndParents.contains(cd)

  /**
   * Here, the lazy type name is recovered from the closure's name.
   * This avoids the use of additional maps.
   */
  val stateTParams = memoAbsClass.tparams.map(_.tp)
  def stateType(tps: Seq[TypeTree] = stateTParams) = {
    SetType(AbstractClassType(memoAbsClass, tps))
  }

  def stateUpdate(elem: Expr, st: Expr) = {
    SetUnion(st, FiniteSet(Set(elem), st.getType.asInstanceOf[SetType].base)) // st@.tn + Set(param2)
  }
}
