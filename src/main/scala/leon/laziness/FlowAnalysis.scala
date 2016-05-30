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

/**
 * Performs type-level analysis to know which types have their targets 
 * completely within scope. 
 * TODO: we can extend this with more sophisticated control-flow analysis
 */
class FunctionTypeAnalysis(p: Program, funsManager: FunctionsManager) {
  
  val escapingTypes = p.units.filter(_.isMainUnit).flatMap{ md =>
    val privateFieldTypes = 
      md.definedClasses.flatMap{ 
      //case cd : ClassDef => cd.fields. 
      
    }
    val rootEscapingTypes = (p.definedClasses ++ p.definedFunctions).flatMap { d =>
      val params = d match {
        case cd: ClassDef => cd.fields
        case fd: FunDef   => fd.params
      }
    }
  }
  
  def isEscapingType(t: FunctionType) = true    
}
