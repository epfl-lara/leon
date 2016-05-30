package leon
package laziness

import invariant.util._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import HOMemUtil._
import ProgramUtil._
import invariant.datastructure._
import purescala.Types._
import purescala.TypeOps._

/**
 * Performs type-level analysis to know which types have their targets
 * completely within scope.
 * TODO: we can extend this with more sophisticated control-flow analysis
 */
class FunctionTypeAnalysis(p: Program, funsManager: FunctionsManager) {

  def isPrivate(d: Definition) = {
    val annots = d match {
      case cd: ClassDef => cd.annotations.toSeq
      case fd: FunDef   => fd.annotations.toSeq
      case _            => Seq()
    }
    annots.contains("Private")
  }
  val escapingTypes = p.units.filter(_.isMainUnit).flatMap { md =>
    // fields and parameters of public classes and methods are accessible from outside, others are not
    (p.definedClasses ++ p.definedFunctions).flatMap {
      case cd: ClassDef if !isPrivate(cd) => cd.typed +: cd.fields.map(_.getType)
      case fd: FunDef if !isPrivate(fd)   => fd.params.map(_.getType)
    }
  }

  /**
   * A function type escapes if it is a **super type** of an escaping type
   */
  def isEscapingType(ft: FunctionType) = escapingTypes.exists{ escType => isSubtypeOf(escType, ft)  }
}
