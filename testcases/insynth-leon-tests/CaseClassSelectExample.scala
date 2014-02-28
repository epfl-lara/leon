import scala.collection.immutable.Set
import leon.annotation._
import leon.lang._

object CaseClassSelectExample { 

  sealed abstract class OptionInt
  case class Some(v : Int) extends OptionInt
  case class None() extends OptionInt
    
  // this won't work
//  sealed abstract class AbsHasVal(v: Int)
//  case class Concrete(x: Int) extends AbsHasVal(x)
  
  def selectIntFromSome(some: Some) = {
    some.v
  }
  
  // this won't work
//  def selectIntFromSome(a: Concrete) = {
//    a.v
//  }

}
