package leon.comparison

import leon.purescala.Definitions.CaseClassDef
import leon.purescala.Expressions.Expr

/**
  * Created by joachimmuth on 25.04.16.
  */
object Utils {

  /**
    * One hard piece is to compare two case clase, because it cannot be normalized like value
    *
    * @return
    */

  def compareClass(classDefB: CaseClassDef, classDef: CaseClassDef): Double ={
    println("COMPARE CASE CLASS")
    println(classDef)
    println(classDef.tparams)
    println(classDef.tparams.map(_.tp.getType))
    println(classDef.parent)
    println(classDef.parent.get.parent)
    1.0
  }
}
