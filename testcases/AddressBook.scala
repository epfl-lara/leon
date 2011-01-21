import scala.collection.immutable.Set
import funcheck.Annotations._
import funcheck.Utils._

// Ongoing work: take Chapter 2 of Daniel Jackson's book,
// adapt the addressbook example from there.
object AddressBook {
  sealed abstract class U1
  case class Name(v : Int) extends U1

  sealed abstract class U2
  case class Addr(v : Int) extends U2

  sealed abstract class U3
  case class Book(addr : Map[Name, Addr]) extends U3
}
