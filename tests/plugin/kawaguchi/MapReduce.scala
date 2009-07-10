package plugin.kawaguchi

/* Example from paper "Type-based Data Structure Verification"
 * http://pho.ucsd.edu/liquid/demo/index2.php */

import funcheck.lib.Specs._

object MapReduce {
  
  /* specification */
  def insert(map: Map[Int, List[Int]], entry: (Int, Int)): Map[Int, List[Int]] = {
    val (key,value) = entry
    map.get(key) match {
      case None => map + ((key, List(value)))
      case Some(vs) => map + ((key, value :: vs)) 
    }
  }
  
  def content(kvs: List[(Int, List[Int])]) = 
    Map.empty[Int, List[Int]] ++ (kvs)
    
  
  /*****************************************/
  
  
  forAll[(List[(Int,List[Int])],(Int,Int))]{p => insert(content(p._1),p._2) == content(insert(p._1,p._2))}
  
  def insert(t: List[(Int,List[Int])], x: (Int,Int)): List[(Int,List[Int])] = {
    val (key,value) = x
    t match {
      case Nil => List((key, List(value)))
      case (k,vs) :: t => 
        if(k == key)
          (k, value :: vs) :: t
        else
          (k,vs) :: (insert(t,x))
    }
  }
  
  def expand(f: Int => List[(Int, Int)], xs: List[Int]): List[(Int,Int)] = xs match {
    case Nil => Nil
    case x :: xs => f(x) ::: expand(f,xs) 
  } 
  
  
  
  def group(kvs: List[(Int, Int)]): List[(Int,List[Int])] = {
    val nil: List[(Int,List[Int])] = Nil
    (nil /: kvs) {
      case (z, a) => insert(z, a)
    }
  }
  
  
  def collapse(f: (Int,Int) => Int, gs: List[(Int, List[Int])]): List[(Int, Int)] = {
    val collapser = {
      x: (Int, List[Int]) => x match {
        case (k, Nil) => assert(false); null
        case (k, v :: vs)  => (k, vs.foldLeft(v)((z: Int,a: Int) => f(z,a)))  
       
      }
    }
    
    gs.map(collapser(_))
  } 
  
  
  def map_reduce(xs: List[Int], mapper: Int => List[(Int, Int)], reducer: (Int,Int) => Int): List[(Int, Int)] = {
    val kvs: List[(Int,Int)] = expand(mapper,xs)
    val gs: List[(Int,List[Int])] = group(kvs)
    val rs  = collapse(reducer, gs)
    rs
  }
  
  
  
  
  def main(args: Array[String]) = {
//    val xs = List.range(1,5)
//    val mapper: Int => List[(Int,Int)] = {x: Int => List((x,x+2), (x,x+3))}
//    val reducer = {(a: Int,b: Int) => a + b}
//    
//    println(map_reduce(xs,mapper,reducer))
  }
  
}
