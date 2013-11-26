import scala.collection.immutable.Set
import leon.lang._
import leon.annotation._

object UseContradictoryLemma {

  def lemma1(x : Int) : Boolean = {
    x == 1
  } holds

  def f(x : Int) : Int = { 
    5
  } ensuring (x => lemma1(x) && x == 1)

}
