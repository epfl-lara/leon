import scala.collection.immutable.Set
import funcheck.Utils._
import funcheck.Annotations._

object UseContradictoryLemma {

  def lemma1(x : Int) : Boolean = {
    x == 1
  } holds

  def f(x : Int) : Int = { 
    5
  } ensuring (x => lemma1(x) && x == 1)

}
