import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Addresses {
  case class Info(
    address: Int,
    zipcode: Int,
    phoneNumber: Int
  )
  
  case class Address(info: Info, priv: Boolean)
  
  sealed abstract class List
  case class Cons(a: Address, tail:List) extends List
  case object Nil extends List

  def content(l: List) : Set[Address] = l match {
    case Nil => Set.empty[Address]
    case Cons(addr, l1) => Set(addr) ++ content(l1)
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
  
  def size(ab: AddressBook): Int = size(ab.business) + size(ab.pers)
  	  
	def addToPers(ab: AddressBook, adr: Address) = AddressBook(ab.business, Cons(adr, ab.pers))
 	  
  def addToBusiness(ab: AddressBook, adr: Address) = AddressBook(Cons(adr, ab.business), ab.pers)
  	    		 
  def isEmpty(ab: AddressBook) = size(ab) == 0
  
  def content(ab: AddressBook) : Set[Address] = content(ab.pers) ++ content(ab.business)
  
  def addressBookInvariant(ab: AddressBook) = allPrivate(ab.pers) && allBusiness(ab.business)
  
  def makeAddressBook(l: List): AddressBook = (l match {
    case Nil => AddressBook(Nil, Nil)
    case Cons(a, l1) => 
      val res = makeAddressBook(l1)
      if (a.priv) AddressBook(res.business, Cons(a, res.pers))
      else AddressBook(Cons(a, res.business), res.pers)
  }) ensuring {
    (res: AddressBook) =>
		  size(res) == size(l) && addressBookInvariant(res)
  }

  def merge(l1: List, l2: List): List = (l1 match {
    case Nil => l2
    case Cons(a, tail) => Cons(a, merge(tail, l2))
  }) ensuring(res => size(res) == size(l1) + size(l2) &&
	     (!allBusiness(l1) || !allBusiness(l2) ||allBusiness(res)) &&
	     (!allPrivate(l1) || !allPrivate(l2) ||allPrivate(res)))

  def mergeAddressBooks(ab1: AddressBook, ab2: AddressBook) = { 
    require(addressBookInvariant(ab1) && addressBookInvariant(ab2))
		choose { (res: AddressBook) =>
		  (size(res) == size(ab1) + size(ab2)) && addressBookInvariant(res)
  	}
  }

}
