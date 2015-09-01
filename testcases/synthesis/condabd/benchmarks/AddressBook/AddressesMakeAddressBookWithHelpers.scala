import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Addresses {
  
  case class Address(a: Int, b: Int, priv: Boolean)
  
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
  
  def addToPers(ab: AddressBook, adr: Address) = AddressBook(ab.business, Cons(adr, ab.pers))
  
  def addToBusiness(ab: AddressBook, adr: Address) = AddressBook(Cons(adr, ab.business), ab.pers)
  
  def size(ab: AddressBook): Int = size(ab.business) + size(ab.pers)
  	  
  	  def content(ab: AddressBook) : Set[Address] = content(ab.pers) ++ content(ab.business)
  	  
  def addressBookInvariant(ab: AddressBook) = allPrivate(ab.pers) && allBusiness(ab.business)
  
  def merge(l1: List, l2: List): List = l1 match {
    case Nil => l2
    case Cons(a, tail) => Cons(a, merge(tail, l2))
  }
   
//  def makeAddressBook(l: List): AddressBook = (l match {
//    case Nil => AddressBook(Nil, Nil)
//    case Cons(a, l1) => {
//      val res = makeAddressBook(l1)
//      if (a.priv) AddressBook(res.business, Cons(a, res.pers))
//      else AddressBook(Cons(a, res.business), res.pers)
//    }
//  }) ensuring {
//    res =>
//	  size(res) == size(l) &&
//	  !hasPrivate(res.business) &&
//	  hasPrivate(res.pers)
//  }
  
//  def makeAddressBook(l: List): AddressBook = (l match {
//    case Nil => AddressBook(Nil, Nil)
//    case Cons(a, l1) => {
//      val res = makeAddressBook(l1)
//      if (a.priv) AddressBook(res.business, Cons(a, res.pers))
//      else AddressBook(Cons(a, res.business), res.pers)
//    }
//  }) ensuring {
//    res =>
//	  size(res) == size(l) &&
//	  (if (size(res.business) > 0) {
//	    !hasPrivate(res.business)
//	  } else true ) &&
//	  (if (size(res.pers) > 0) {
//	    hasPrivate(res.pers)
//	  } else true )
//  }
//  
//  def makeAddressBook(l: List): AddressBook = 
//		choose {
//    (res: AddressBook) =>
//		  size(res) == size(l) &&
//		  (if (size(res.business) > 0) {
//		    !hasPrivate(res.business)
//		  } else true ) &&
//		  (if (size(res.pers) > 0) {
//		    hasPrivate(res.pers)
//		  } else true )
//  }
  
  def makeAddressBook(l: List): AddressBook = choose {
    (res: AddressBook) =>
		  size(res) == size(l) &&
		  allPrivate(res.pers) && allBusiness(res.business) &&
		  content(res) == content(l)
  }
  
}
