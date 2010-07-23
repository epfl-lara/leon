package setconstraints

import scala.collection.mutable.{Map, HashMap}

import purescala.Definitions._
import setconstraints.Trees._

object LabelProgram {

  def apply(pgm: Program): (Map[ClassTypeDef, VariableType],
    Map[FunDef, (Seq[VariableType], VariableType)]) =
      (labelTypeHierarchy(pgm), labelFunction(pgm))


  private def labelFunction(pgm: Program): Map[FunDef, (Seq[VariableType], VariableType)] = {
    val hm = new HashMap[FunDef, (Seq[VariableType], VariableType)]
    pgm.definedFunctions.foreach(fd => {
      val varTypes = (fd.args.map(vd => freshVar(fd.id.name + "_arg_" + vd.id.name)), freshVar(fd.id.name + "_return"))
      hm.put(fd, varTypes)
    })
    hm
  }

  private def labelTypeHierarchy(pgm: Program): Map[ClassTypeDef, VariableType] = {
    val hm = new HashMap[ClassTypeDef, VariableType]
    pgm.definedClasses.foreach(clDef => hm.put(clDef, freshVar(clDef.id.name)))
    hm
  }
}
