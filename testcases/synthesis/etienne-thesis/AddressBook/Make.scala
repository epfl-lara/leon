import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object AddressBookMake {

  case class Address[A](info: A, priv: Boolean)

  sealed abstract class AddressList[A] {
    def size: BigInt = {
      this match {
        case Nil() => BigInt(0)
        case Cons(head, tail) => BigInt(1) + tail.size
      }
    } ensuring { res => res >= 0 }

    def content: Set[Address[A]] = this match {
      case Nil() => Set[Address[A]]()
      case Cons(addr, l1) => Set(addr) ++ l1.content
    }
  }

  case class Cons[A](a: Address[A], tail: AddressList[A]) extends AddressList[A]
  case class Nil[A]() extends AddressList[A]

  def allPersonal[A](l: AddressList[A]): Boolean = l match {
    case Nil() => true
    case Cons(a, l1) =>
      if (a.priv) allPersonal(l1)
      else false
  }

  def allBusiness[A](l: AddressList[A]): Boolean = l match {
    case Nil() => true
    case Cons(a, l1) =>
      if (a.priv) false
      else allBusiness(l1)
  }

  case class AddressBook[A](business: AddressList[A], personal: AddressList[A]) {
    def size: BigInt = business.size + personal.size

    def content: Set[Address[A]] = business.content ++ personal.content

    def invariant = {
      allPersonal(personal) && allBusiness(business)
    }
  }

  def makeAddressBook[A](as: AddressList[A]): AddressBook[A] = {
    choose( (res: AddressBook[A]) => res.content == as.content && res.invariant )
  }
}
