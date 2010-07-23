package setconstraints

import purescala.Definitions._
import purescala.TypeTrees.ClassType
import setconstraints.Trees._

import scala.collection.mutable.HashMap

object ADTExtractor {

  def apply(pgm: Program): HashMap[ClassTypeDef, SetType] = {
    val hm = new HashMap[ClassTypeDef, SetType]
    var dcls = pgm.definedClasses
    while(!dcls.isEmpty) {
      val curr = dcls.head
      if(curr.isInstanceOf[AbstractClassDef]) {
        hm.put(curr, freshVar(curr.id.name))
        dcls = dcls.filterNot(_ == curr)
      } else if(curr.isInstanceOf[CaseClassDef]) {
        val name = curr.id.name
        val fields = curr.asInstanceOf[CaseClassDef].fields
        try {
          val l = fields.map(vd => hm(vd.tpe.asInstanceOf[ClassType].classDef)).toList
          hm.put(curr, ConstructorType(name, l))
          dcls = dcls.filterNot(_ == curr)
        } catch {
          case _: NoSuchElementException => {
            dcls = dcls.tail ++ List(dcls.head)
          }
        }
      } else error("Found a class which is neither an AbstractClassDef nor a CaseClassDef")
    }
    hm
  }

}
