

object HeapTest extends Application {

  /*
  import org.scalacheck.Prop
  import org.scalacheck.Prop._
  forAll{(l1: List[Int], l2: List[Int]) => (l1 ++ l2).size == l1.size + l2.size}
  */
  
  
  //import funcheck.lib.Specs._
//  import org.scalacheck.Prop._
//  import org.scalacheck.Test.check
//  val prop = forAll{ p: Int => forAll{ v: Int => v + p == p + v}}
//  check(prop)
                               
    //import org.scalacheck.Prop._                                         
	import funcheck.lib.Specs._
    forAll{ p: Int => forAll{ v: Int => v + p == p + v}}                                         
//  forAll[(Int,Int)]{it=> true}
//  forAll{it: List[Int] => true}
  
  
  //forAll[(Array[Int], Array[Int])]{ lists => (lists._1 ++ lists._2).size == lists._1.size + lists._2.size}
  
  
  //val p = 3
  
//  import org.scalacheck.Prop._
//  import org.scalacheck.ConsoleReporter.testStatsEx
//  import org.scalacheck.Test.check
  
  //p >= 0 ==> p > 0
  
  
  //forAll{ p: Int => p > 1 ==> p >= 0}
  
//  val prop = forAll{ p: Int => p > 1 ==> p >= 0}
//  testStatsEx(check(prop))
  //Prop.forAll{ p: Int => Prop.==>(p >= 0, p > 0)}
  
  //works
//  forAll[Int]( p => forAll[Int]( v => v + p == p + v))
//  forAll[(Int,Int)]( p => p._1 + p._2 == p._2 + p._1)

  //fails!
//  forAll[Int]( p => p == 0)
  
  
}