package setconstraints

import purescala.Definitions._

object Tools {

  def childOf(root: ClassTypeDef, classes: Seq[ClassTypeDef]) = classes.filter(_.parent == root)

  def toCaseClasses(classes: Seq[ClassTypeDef]): Seq[CaseClassDef] = 
    classes.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])

  def fix[A](f: (A) => A, a: A): A = {
    val res = f(a)
    if(res == a) a else fix(f, res)
  }
}
