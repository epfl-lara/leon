object DisjointSet {
  
  sealed abstract class Tlist
  case class Cons(head: InvTree, tail: Tlist) extends Tlist
  case class Nil() extends Tlist
  
  sealed abstract class InvTree
  case class Empty() extends InvTree
  case class Node(v: Int, p: InvTree, r: Int) extends InvTree
  
  sealed abstract class DisjSet
  //case class NullSet() extends  DisjSet
  case class Buckets(roots: Tlist) extends DisjSet  
  
  
  def twopower(x: Int) : Int = {    
    if(x < 1) 1    
    else      
      2* twopower(x - 1)
  } /*ensuring (res => !(x >= 0) || res >= 1)*/
  
  def Size(t: InvTree) : Int = { 
    t match {
      case Node(v,p,r) => Size(c) + 1
      case Empty() => 0
    }
  } /*ensuring (res => res >= 0)*/
  
  def Size(l: Tlist) : Int = {
    l match {
      case Cons(head,tail) => Size(head) + Size(tail)
      case Nil() => 0
    }
  } ensuring (res => res >= 0)
  
  def Size(ds: DisjSet) : Int = {
    ds match {
      case Buckets(roots) => Size(roots)      
    }
  }
  
  def DisjSetInvariant(t: InvTree, prnt: InvTree): Boolean  = {
	  t match {
	    case Node(v,c,p,r) => DisjSetInvariant(c,t)  && (p == prnt) && 
	    						r >= 0 && twopower(r) <= Size(t) && 
	    						(p match { case Node(_,_,_,u) => u == r + 1
	    									case _ => true })
	    case _ => true
	  }
  }
  
  def DisjSetInvariant(l: Tlist,prnt: InvTree): Boolean  = {
	l match {
      case Cons(head,tail) => DisjSetInvariant(head,prnt) && DisjSetInvariant(tail,prnt)
      case _ => true
    }
  }
  
  def DisjSetInvariant(ds: DisjSet): Boolean  = {
    ds match {
      case Buckets(roots) => DisjSetInvariant(roots,Empty())
    }    
  }
  
  /*def RootHasEmptyParent(l: Tlist): Boolean  = {
	l match {
      case Cons(head,tail) =>
        (head match {
          case Empty() => true
          case Node(_,_,Empty(),_) => true
          case _ => false
        }) && RootHasEmptyParent(tail)
      case _ => true
    }
  }*/
  
  /*def RootsHaveEmptyParents(ds: DisjSet): Boolean  = {
    ds match {
      case Buckets(roots) => RootHasEmptyParent(roots)
    }    
  }*/
  
  
  def Contains(x : InvTree, l: Tlist) : Boolean = {
    l match {
      case Cons(head,tail) => (x == head) ||Contains(x,tail)
      case Nil() => false
    }
  } ensuring (res => !res || Size(x) <= Size(l))
  
  /*def Belongs(l : Tlist, ds: DisjSet) : Boolean = {
    l match {
      case Cons(head,tail) => Belongs(head,ds) && Belongs(tail,ds)
      case Nil() => true
    } 
  }*/
  
  /*def Belongs(x : Tree, ds: DisjSet) : Boolean = {
     val root = FindRoot(x,ds)._1
    	  ds match {
            case Buckets(roots) => Contains(root,roots)      
          }        
  } ensuring (res => !res || Size(x) <= Size(ds))*/
  
  def GetRoots(ds: DisjSet) : Tlist = {
    ds match {
       case Buckets(roots) => roots      
    }
  }
  
  /*def Belongs(x : Tree, ds: DisjSet) : Boolean = {
    x match { 
      case Node(_,_,p,_) => Belongs(p,ds)
      case Empty() =>
        
    }     	          
  }*/  
  
  
  def Rank(t: InvTree) : Int = {
    t match {
            case Node(_,_,_,r) => r
            case Empty() => 0
          }
  }
  
  def FindRoot(t: InvTree, ds: DisjSet) : (InvTree,Int) = {
    t match {
      case Empty() => (t,0)
      case Node(v,c,p,r) => {
        p match {
          case Empty() => (t,0)
          case _ => {
        	  val (rt,i) = FindRoot(p,ds)
        	  (rt,i+1)            
          }
        }
      } 
    }
  } ensuring(res => !(DisjSetInvariant(ds) && Contains(res._1,GetRoots(ds))) || 
      (Size(res._1) <= Size(ds) &&
          (res._2 + Rank(t) == Rank(res._1)) 
           /*&& twopower(Rank(res._1)) <= Size(res._1)*/            
          ))       
  
  def RemoveElement(l: Tlist, elem: InvTree) : Tlist = {
    l match {
      case Cons(head,tail) => if(head == elem) tail else Cons(head,RemoveElement(tail,elem))
      case _ => l
    }
  }
  
  def RemoveRoot(ds: DisjSet,rt: InvTree): DisjSet = {
    ds match {
      case Buckets(roots) => Buckets(RemoveElement(roots, rt))
    }
  }
  
  def Union(x: InvTree, y: InvTree, ds: DisjSet) : DisjSet = {	  

	  FindRoot(x,ds)._1 match {
	    case Empty() => ds
	    case t1@Node(v1,c1,p1,r1) => 
	    {
	    	FindRoot(y,ds)._1 match {
	    	  case Empty() => ds
	    	  case t2@Node(v2,c2,p2,r2) =>
	    	  {
	    		  if(t1 == t2) ds
	    		  else if(r1 == r2 || r1 > r2) {
	    		    	    		    
	    			  val ds1 = RemoveRoot(RemoveRoot(ds,t2),t1)
	    			  val newt = Node(v1,Cons(t2,c1),p1, if(r1 > r2) r1 else r1 + 1)
	    			  ds1 match {
	    			  	case Buckets(roots) => Buckets(Cons(newt,roots)) 
	    			  }
	    		  }
	    		  else {	    		    
	    		    val ds1 = RemoveRoot(RemoveRoot(ds,t2),t1)
	    			  val newt = Node(v2,Cons(t1,c2),p2, r2)
	    			  ds1 match {
	    			  	case Buckets(roots) => Buckets(Cons(newt,roots)) 
	    			  }
	    		  }	    		   	    		    
	    	  }
	    	}
	    }
	  }        	   
  }      

  def Find(x: InvTree, ds: DisjSet): (InvTree,Int) = {
    /*require(DisjSetInvariant(ds) && Belongs(x,ds))*/
    
    FindRoot(x,ds)    
    
  } /*ensuring(res => */
    			/*twopower(res._2) <= Size(res._1) && */
    			/*Size(res._1) <= Size(ds)*/    	
    /*twopower(res._2) <= Size(ds)*/
    //)  
}