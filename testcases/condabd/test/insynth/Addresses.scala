import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Addresses {
  
  case class Address(aComp: Int, bComp: Int, priv: Boolean)
  
  sealed abstract class List
  case class Cons(a: Address, tail:List) extends List
  case object Nil extends List

  def setA(l: List) : Set[Address] = l match {
    case Nil => Set.empty[Address]
    case Cons(a, l1) => Set(a) ++ setA(l1)
  }
  
	def size(l: List) : Int = l match {
	  case Nil => 0
	  case Cons(head, tail) => 1 + size(tail)
	}
	
  def allPrivate(l: List): Boolean = l match {
    case Nil => true
    case Cons(a, l1) =>
      if (a.priv) allPrivate(l1)
      else false
  }
	
  def allBusiness(l: List): Boolean = l match {
    case Nil => true
    case Cons(a, l1) =>
      if (a.priv) false
      else allBusiness(l1)
  }

  case class AddressBook(business : List, pers : List)
  
  def addToPers(ab: AddressBook, adr: Address) = AddressBook(ab.business, Cons(adr, ab.pers))
  
  def addToBusiness(ab: AddressBook, adr: Address) = AddressBook(Cons(adr, ab.business), ab.pers)
  
  def size(ab: AddressBook): Int = size(ab.business) + size(ab.pers)
  	  
  def makeAddressBook(l: List): AddressBook = 
		choose {
    (res: AddressBook) =>
		  size(res) == size(l) &&
		  allPrivate(res.pers) && allBusiness(res.business)
  }
  
}
