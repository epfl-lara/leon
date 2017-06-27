import leon.annotation._
import leon.annotation.grammar._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar.Grammar._
import leon.collection._

object AddressBookMerge {

  @production(1)
  def mkAddress[A](info: A, priv: Boolean): Address[A] = Address(info, priv)

  @production(1)
  def mkAddressBook[A](b: List[Address[A]], p: List[Address[A]]): AddressBook[A] = AddressBook(p, b)
  
  @production(100)
  def lUnion[A](l1: List[A], l2: List[A]): List[A] = union(l1, l2)

  def union[A](l1: List[A], l2: List[A]): List[A] = { l1 match {
    case Nil() => l2
    case Cons(h, t) => Cons(h, union(t, l2))
  }} ensuring { res => res.content == l1.content ++ l2.content }

  case class Address[A](info: A, priv: Boolean)

  def allPersonal[A](l: List[Address[A]]): Boolean = l match {
    case Nil() => true
    case Cons(a, l1) =>
      if (a.priv) allPersonal(l1)
      else false
  }

  def allBusiness[A](l: List[Address[A]]): Boolean = l match {
    case Nil() => true
    case Cons(a, l1) =>
      if (a.priv) false
      else allBusiness(l1)
  }

  case class AddressBook[A](business: List[Address[A]], personal: List[Address[A]]) {
    def size: BigInt = business.size + personal.size

    def content: Set[Address[A]] = business.content ++ personal.content

    def invariant = {
      allPersonal(personal) && allBusiness(business)
    }
  }

  def merge[A](a1: AddressBook[A], a2: AddressBook[A]): AddressBook[A] = {
    require(a1.invariant && a2.invariant)
    // AddressBook(a1.business ++ a2.business, a1.personal ++ a2.personal)
    ???[AddressBook[A]]
  } ensuring {
    (res: AddressBook[A]) =>
      res.personal.content == (a1.personal.content ++ a2.personal.content) &&
      res.business.content == (a1.business.content ++ a2.business.content) &&
      res.invariant
  }

}
