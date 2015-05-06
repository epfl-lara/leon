package leon.lang
import leon.annotation._

object Map {
  @library
  def empty[A,B] = Map[A,B]()

   @ignore
   def apply[A,B](elems: (A,B)*) = {
     new Map[A,B](scala.collection.immutable.Map[A,B](elems : _*))
   }
}

@ignore
case class Map[A, B](val theMap: scala.collection.immutable.Map[A,B]) {
  def apply(k: A): B = theMap.apply(k)
  def ++(b: Map[A, B]): Map[A,B] = new Map (theMap ++ b.theMap)
  def updated(k: A, v: B): Map[A,B] = new Map(theMap.updated(k, v))
  def contains(a: A): Boolean = theMap.contains(a)
  def isDefinedAt(a: A): Boolean = contains(a)
}
