package setconstraints

import purescala.Definitions._

object Tools {

  def childOf(root: ClassTypeDef, classes: Seq[ClassTypeDef]) = classes.filter(_.parent == root)

  def toCaseClasses(classes: Seq[ClassTypeDef]): Seq[CaseClassDef] = 
    classes.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])
}
