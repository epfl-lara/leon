import funcheck.lib.Specs

object HeapTest extends Application {
 
  //works
  Specs.forAll[(Int,Int)]( p => p._1 + p._2 == p._2 + p._1)

  //fails!
  Specs.forAll[Int]( p => p == 0)

  
}