import leon.Utils._

/*object MyList {

  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List
  
  def size(l: List): Int = (l match {
    case Cons(_, tail) => 1 + size(tail)
    case Nil() => 0
  }) ensuring (res => res >= 0)
  
  def insert(l: List, e: Int): (List,Int) = (l match {    
    case Cons(n,tail) =>
      val (e,t) = insert(tail,e)
      (Cons(n,e), 3 +t)             
    case Nil() => (Cons(e,Nil()),3)
  }) ensuring (res =>  res._2 <= 3*size(l) +3)
  
  
  def traverse(l: List): (List,Int) = (l match {    
    case Cons(n,tail) =>
      val (e,t) = traverse(tail)
      (Cons(n,e),t+3)             
    case Nil() => (Nil(),3)
  }) ensuring (res => res._2 <= 3*size(l) + 3)
  
  //computes x * y
  def mult(x: Int, y: Int) : Int = ({    
    if(x == 0) 0
    else y + mult(x-1,y)
  }) ensuring(res => (x < 0 || y < 0) || (res >= 0))
  
  def ContrivedInsert(l: List, orig: List, e: Int): (List,Int) = (l match {    
    case Cons(n,tail) => { 
    	val (l1,t1) = traverse(orig)
    	val (l2,t2) = ContrivedInsert(tail,orig,e)
    	(Cons(n,l2),t1+t2+3)
    }
    case Nil() => (Cons(e,Nil()),3)
  }) ensuring (res => res._2 <= 3 * size(l) * size(orig) + 7 * size(l) + 3)  
}*/

object MyList {
  case class Nil() extends List

  case class Cons(head: Int, tail: List) extends List

  sealed abstract class List

  def ContrivedInsert1(l : List, orig : List, e : Int) : (List, Int) = ( {
    val t = 1
    l match {
      case Cons(head,tail) =>
      locally {
        val t12 =  {
          val t13 =  {          
            val t14 = ContrivedInsert1(tail, orig, e)
            (Cons(head, t14._1), (t14._2 + 2))
          }
          
          (t13._1, (t13._2 + (locally {
            val t15 = traverse1(orig)
            (t15._1, (1 + t15._2))
          }
          ._2 + 1)))
        }
        
        (t12._1, (t + t12._2))
      }
      case Nil()=>(Cons(e, Nil()), (t + 2))      
    } 
  }
   ensuring(res => (res._2 <= (((3 * mult1(size1(l)._1, size1(orig)._1)._1) + (7 * size1(l)._1)) + 3))))

  def mult1(x : Int, y : Int) : (Int, Int) = ( {
    val t16 = 1
    if ((x == 0)) {
      (0, t16)
    } else {
      {
        val t23 = {
          val t24 = mult1((x - 1), y)
          ((y + t24._1), (t24._2 + 1))
        }
        
        (t23._1, (t16 + t23._2))
      }
      
    }
  }
   ensuring(res1 => ((x < 0) || (y < 0) || (res1._1 >= 0))))

  def traverse1(l : List) : (List, Int) = ( {
    val t25 = 1
    l match {
      case Cons(head,tail) =>
      {
        val t32 = {
          val t33 = traverse1(tail)
          (Cons(head, t33._1), (t33._2 + 2))
        }
        
        (t32._1, (t25 + t32._2))
      }
      case Nil() => (Nil(), (t25 + 1))
    } 
  }
   ensuring(res2 => (res2._2 <= ((3 * size1(l)._1) + 3))))

  def size1(l : List) : (Int, Int) = ( {
    val t34 = 1
    l match {
      case Cons(head,tail) =>
      {
        val t40 = {
          val t41 = size1(tail)
          ((1 + t41._1), (t41._2 + 1))
        }
        
        (t40._1, (t34 + t40._2))
      }
      case Nil() =>(0, t34) 
    } 
  }
   ensuring(res3 => (res3._1 >= 0)))
}
