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
  
  def sizeA(ab: AddressBook): Int = size(ab.business) + size(ab.pers)
  	  
  def addToPers(ab: AddressBook, adr: Address) = ({
    require(addressBookInvariant(ab))
    AddressBook(ab.business, Cons(adr, ab.pers))
  }) ensuring(res => addressBookInvariant(res))
  	  
  def addToBusiness(ab: AddressBook, adr: Address) = ({
    require(addressBookInvariant(ab))
    AddressBook(Cons(adr, ab.business), ab.pers)
  }) ensuring(res => addressBookInvariant(res))
  	    		 
  def isEmpty(ab: AddressBook) = sizeA(ab) == 0
  
  def contentA(ab: AddressBook) : Set[Address] = content(ab.pers) ++ content(ab.business)
  
  def addressBookInvariant(ab: AddressBook) = allPrivate(ab.pers) && allBusiness(ab.business)
  
  def merge(l1: List, l2: List): List = (l1 match {
    case Nil => l2
    case Cons(a, tail) => Cons(a, merge(tail, l2))
  }) ensuring(res => size(res)==size(l1) + size(l2) && 
                     (!allPrivate(l1) || !allPrivate(l2) || allPrivate(res)) &&
                     (!allBusiness(l1) || !allBusiness(l2) || !allBusiness(res))
             )
  
  def mergeAddressBooks(ab1: AddressBook, ab2: AddressBook) = { 
    require(addressBookInvariant(ab1) && addressBookInvariant(ab2))
		choose { (res: AddressBook) =>
		  (sizeA(res) == sizeA(ab1) + sizeA(ab2)) && addressBookInvariant(res)
  	}
  }
  
}
