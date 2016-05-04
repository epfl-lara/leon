package leon.comparison

import leon.purescala.Definitions.{CaseClassDef, ClassDef}
import leon.purescala.Expressions.{CaseClass, Expr}
import leon.purescala.Types.{ClassType, TypeTree}

/**
  * Created by joachimmuth on 25.04.16.
  */
object Utils {


  /**
    * One hard piece is to compare two case clase, because it cannot be normalized like value
    *
    * @return
    */

  def compareClassDef(classA: ClassDef, classB: ClassDef): Double = {
    (classA, classB) match {
      case (a,b) if (a.isAbstract && b.isAbstract) =>
        if (a.knownCCDescendants.size == b.knownCCDescendants.size) 1.0
        else 0.0
      case (a: CaseClassDef, b:CaseClassDef) =>
        compareCaseClassDef(a,b)
      case _ =>   0.0

    }
  }

  def compareTypeTree(typeA: TypeTree, typeB: TypeTree): Double = (typeA, typeB) match {
    case (a: ClassType, b: ClassType) => compareClassDef(a.classDef, b.classDef)
    case _ => 0.0
  }


  /**
    * Combine number of parameter, of parameter of its own type and of the type of its parent
    * (to be improved for CaseClass without argument, for example match with parent)
    * @param a
    * @param b
    * @return
    */
  def compareCaseClassDef(a: CaseClassDef, b: CaseClassDef): Double = {
    val ownTypeA: Int = argumentsOfOwnType(a)
    val ownTypeB: Int = argumentsOfOwnType(b)
    val parentTypeA : Int = argumentsOfParentType(a)
    val parentTypeB: Int = argumentsOfParentType(b)

    val percentageMatch: Double = percentMatch(a.fields.size, b.fields.size) *
    percentMatch(ownTypeA, ownTypeB) * percentMatch(parentTypeA, parentTypeB)

    percentageMatch
  }


  /**
    * Count how many occurrences of its own type appear in its arguments
    * (to be improved if multiples types)
    * @param a the case class
    * @return
    */
  def argumentsOfOwnType(a: CaseClassDef): Int = {
    a.fields.map(_.getType).count(a.tparams.map(_.tp.getType).contains(_))
  }

  /**
    * Count how many occurrences of its parent type appear in its arguments
    * @param a
    * @return
    */
  def argumentsOfParentType(a: CaseClassDef): Int = a match {
    case _ if a.hasParent => a.fields.map(_.getType).count(_ == a.parent.get.getType)
    case _ => 0
  }

  def percentMatch(a: Int, b: Int): Double = {
    if(a == 0 && b == 0) 1.0
    else if (a == 0 || b == 0) 0.0
    else Math.min(a.toDouble/b.toDouble, b.toDouble/a.toDouble)
  }


  def mean(a: Double): Double = a
  def mean(a: Double, b: Double): Double = (a + b) / 2
  def mean(a: Double, b: Double, c: Double): Double = (a + b + c) / 3
  def mean(a: Double, b: Double, c: Double, d: Double): Double = (a + b + c + d) / 3
  def mean(list : List[Double]): Double = list.foldLeft(0.0)(_+_) / list.size.toDouble
}
