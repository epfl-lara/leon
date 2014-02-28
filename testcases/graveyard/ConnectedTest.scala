import scala.collection.immutable.Set
import leon.lang._
import leon.annotation._

object VerySimple {
		sealed abstract class L0
		case class Adad( a: L3) extends L0

    sealed abstract class L1
    case class Cons(a : L2, b : L3) extends L1
    case class Nil() extends L1

		sealed abstract class L6
		case class Adadasdad(b : L5) extends L6



    sealed abstract class L2
    case class IPCons(a : L4) extends L2 
    case class IPNil() extends L2


		sealed abstract class L5
		case class sada55( a: L2, b : L6) extends L5



    sealed abstract class L3
    case class IP(a : L0) extends L3

    sealed abstract class L4
    case class Hopa(mizerie: L3 , a : L1) extends L4

}
