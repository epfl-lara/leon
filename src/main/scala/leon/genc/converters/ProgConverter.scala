/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package converters

import purescala.Common._
import purescala.Definitions._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

private[converters] trait ProgConverter {
  this: Converters with MiniReporter =>

  val prog: Program // the program to be converted
  // This is needed as a "global" for the converters mechanism
  // to work properly we punctually need to fetch some specific
  // data from this program.

  // Initially, only the main unit is processed but if it has dependencies in other
  // units, they will be processed as well (and their dependencies as well). However,
  // due to the state of the converter (e.g. function context) we don't do it recursively
  // but iteratively until all required units have been processed.
  // See markUnitForProcessing and processRequiredUnits.
  private var unitsToProcess = Set[UnitDef]()
  private var processedUnits = Set[UnitDef]()

  // Global data: keep track of the custom types and functions of the input program
  // Using sequences and not sets to keep track of order/dependencies
  private var typedefs = Seq[CAST.Typedef]() // typedef to standard types only
  private var enums = Seq[CAST.Enum]()
  private var types = Seq[CAST.TypeWithId]() // both structs and unions
  private var functions = Seq[CAST.Fun]()
  // Includes don't need specific orders, hence we use a set
  private var includes = Set[CAST.Include]() // for manually defined functions


  def registerInclude(incl: CAST.Include) {
    includes = includes + incl
  }

  def registerTypedef(typedef: CAST.Typedef) {
    if (!typedefs.contains(typedef)) {
      typedefs = typedefs :+ typedef
    }
  }

  // Return the manual C typedef contained in the class annotation, if any.
  def getTypedef(cd: ClassDef): Option[CAST.Typedef] = {
    import ExtraOps._

    if (cd.isManuallyTyped) {
      val manualType = cd.getManualType
      val typedef = CAST.Typedef(convertToId(cd.id), CAST.Id(manualType.alias))

      if (!manualType.include.isEmpty)
        registerInclude(CAST.Include(manualType.include))

      registerTypedef(typedef)

      Some(typedef)
    } else None
  }

  def registerEnum(enum: CAST.Enum) {
    debug(s"Registering enum $enum")
    enums = enums :+ enum
  }

  def registerType(typ: CAST.TypeWithId) {
    debug(s"Registering type $typ")

    if (getType(typ.id).isDefined)
      internalError(s"Type $typ redefined")

    types = types :+ typ
  }

  def getType(id: CAST.Id): Option[CAST.Type] = types find { _.id == id }

  def getStruct(id: CAST.Id): Option[CAST.Struct] = getType(id) match {
    case Some(s: CAST.Struct) => Some(s)
    case Some(x) => internalError(s"$id matches something $x: ${x.getClass} and not a CAST.Struct")
    case None => None
  }

  def registerFun(fun: CAST.Fun) {
    // Functions should not get defined multiple times as this
    // would imply invalidating funExtraArgss
    if (functions contains fun)
      internalError(s"Function ${fun.id} defined more than once")
    else
      functions = functions :+ fun
  }

  // Mark a given unit as dependency
  def markUnitForProcessing(unit: UnitDef) {
    if (!processedUnits.contains(unit)) {
      unitsToProcess = unitsToProcess + unit
    }
  }

  def collectIfNeeded(fd: FunDef) {
    val funName = fd.id.uniqueName
    if (!functions.find{ _.id.name == funName }.isDefined) {
      val uOpt = prog.units find { _ containsDef fd }
      val u = uOpt getOrElse { internalError(s"Function $funName was defined nowhere!") }

      debug(s"\t$funName is define in unit ${u.id}")

      markUnitForProcessing(u)
    }
  }

  def convertToProg: CAST.Prog = {
    // Print some debug information about the program's units
    val unitNames = prog.units map { u => (if (u.isMainUnit) "*" else "") + u.id }
    debug(s"Input units are: " + unitNames.mkString(", "))

    val mainUnits = prog.units filter { _.isMainUnit }

    if (mainUnits.size == 0) fatalError("No main unit in the program")
    if (mainUnits.size >= 2) fatalError("Multiple main units in the program")

    val mainUnit = mainUnits.head

    // Start by processing the main unit
    // Additional units are processed only if a function from the unit is used
    markUnitForProcessing(mainUnit)
    processRequiredUnits()

    CAST.Prog(includes, typedefs, enums, types, functions)
  }

  // Process units until dependency list is empty
  private def processRequiredUnits() {
    while (!unitsToProcess.isEmpty) {
      // Take any unit from the dependency list
      val unit = unitsToProcess.head
      unitsToProcess = unitsToProcess - unit

      // Mark it as processed before processing it to prevent infinite loop
      processedUnits = processedUnits + unit
      collectSymbols(unit)
    }
  }

  // Look for function and structure definitions
  private def collectSymbols(unit: UnitDef) {
    debug(s"Converting unit ${unit.id} which tree is:\n$unit")

    implicit val defaultFunCtx = FunCtx.empty

    // Note that functions, type declarations or typedefs are registered in convertTo*
    unit.defs foreach {
      case ModuleDef(id, defs, _) =>
        defs foreach {
          case fd: FunDef => convertToFun(fd)

          case cd: ClassDef => convertToType(cd)

          case x =>
            implicit val pos = x.getPos
            val prefix = s"[unit = ${unit.id}, module = $id]"
            CAST.unsupported(s"$prefix Unexpected definition $x: ${x.getClass}")
        }

      case cc: CaseClassDef => convertToType(cc)

      case x =>
        implicit val pos = x.getPos
        val prefix = s"[unit = ${unit.id}]"
        CAST.unsupported(s"$prefix Unexpected definition $x: ${x.getClass}")
    }
  }

}

