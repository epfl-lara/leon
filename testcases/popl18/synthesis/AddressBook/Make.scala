import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.annotation.grammar._
import leon.grammar.Grammar._
import leon.collection._

object AddressBookMake {

  @production(1)
  def mkAddress[A](info: A, priv: Boolean): Address[A] = Address(info, priv)

  @production(1)
  def mkAddressBook[A](b: List[Address[A]], p: List[Address[A]]): AddressBook[A] = AddressBook(p, b)

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

  def makeAddressBook[A](as: List[Address[A]]): AddressBook[A] = {
    choose( (res: AddressBook[A]) => res.content == as.content && res.invariant )

 /*   as match {
      case Nil() => AddressBook[A](Nil[A](), Nil[A]())
      case Cons(x, xs) =>
        val AddressBook(b, p) = makeAddressBook(xs)
        if(x.priv) AddressBook(b, Cons(x, p))
        else AddressBook(Cons(x, b), p)
    }

  } ensuring { 
    res => res.content == as.content && res.invariant */
  }


}
