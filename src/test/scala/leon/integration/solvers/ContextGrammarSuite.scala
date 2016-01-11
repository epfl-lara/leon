package leon
package integration.solvers

import org.scalatest.FunSuite
import org.scalatest.Matchers
import leon.test.helpers.ExpressionsDSL
import leon.solvers.string.StringSolver
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Common.Identifier
import scala.collection.mutable.{HashMap => MMap}
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import org.scalatest.concurrent.Timeouts
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.time.SpanSugar._
import org.scalatest.FunSuite
import org.scalatest.concurrent.Timeouts
import org.scalatest.concurrent.ScalaFutures
import org.scalatest.time.SpanSugar._

/**
 * @author Mikael
 */
class ContextGrammarSuite extends FunSuite with Matchers with ScalaFutures {
  
  val ctx = new synthesis.grammars.ContextGrammar[String, String]
  import ctx._
  
  val A = NonTerminal("A")
  val B = NonTerminal("B")
  val C = NonTerminal("C")
  val x = Terminal("x", "")
  val y = Terminal("y", "")
  val z = Terminal("z", "")
  
  test("Horizontal Markovization Simple")  {
    val xA = A.copy(hcontext = List(x))
    val grammar1 = 
      Grammar(Seq(A), Map(A -> Expansion(Seq(Seq(x, A), Seq(y)))))
    val grammar2 =
      Grammar(Seq(A), Map(A -> Expansion(Seq(Seq(x, xA), Seq(y)))))
        
    grammar1.markovize_horizontal() should equal (grammar2)
    grammar2.markovize_horizontal() should equal (grammar2)
  }
  test("Horizontal Markovization Double")  {
    val BA = A.copy(hcontext = List(B))
    val AB = B.copy(hcontext = List(A))
    
    val grammar1 = 
      Grammar(Seq(A, B),
          Map(A -> Expansion(Seq(Seq(B, A), Seq(y))),
              B -> Expansion(Seq(Seq(x)))
              ))
    val grammar2 =
      Grammar(Seq(A, AB),
          Map(A -> Expansion(Seq(Seq(B, BA), Seq(y))),
              B -> Expansion(Seq(Seq(x)))
              ))

    grammar1.markovize_horizontal() should equal (grammar2)
    grammar2.markovize_horizontal() should equal (grammar2)
  }
  
  test("Vertical Markovization simple") {
    val AA = A.copy(vcontext = List(A))
    val AAA = AA.copy(vcontext = List(A, A))
    val grammar1 = 
      Grammar(Seq(A), Map(A -> Expansion(Seq(Seq(x, A), Seq(y)))))
    val grammar2 =
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, AA), Seq(y))),
              AA -> Expansion(Seq(Seq(x, AA), Seq(y)))))
    val grammar3 =
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, AA), Seq(y))),
              AA -> Expansion(Seq(Seq(x, AAA), Seq(y))),
              AAA -> Expansion(Seq(Seq(x, AAA), Seq(y)))))
    
    grammar1.markovize_vertical() should equal (grammar2)
    grammar2.markovize_vertical() should equal (grammar3)
  }
  
  test("Vertical Markovization double") {
    val AA = A.copy(vcontext = List(A))
    val BA = A.copy(vcontext = List(B))
    val AB = B.copy(vcontext = List(A))
    val BB = B.copy(vcontext = List(B))
    
    val grammar1 = 
      Grammar(Seq(A, B),
          Map(A -> Expansion(Seq(Seq(x, B), Seq(y))),
              B -> Expansion(Seq(Seq(z, A), Seq(x)))))

    val grammar2 =
      Grammar(Seq(A, B),
          Map(A -> Expansion(Seq(Seq(x, AB), Seq(y))),
              BA -> Expansion(Seq(Seq(x, AB), Seq(y))),
              AB -> Expansion(Seq(Seq(z, BA), Seq(x)))))
    
    grammar1.markovize_vertical() should equal (grammar2)
  }
  
  /*test("Horizontal Markovization multiple") {
    val g = Grammar(Seq(A, A, A),
        Map(A -> Expansion(Seq(Seq(B, C), Seq(z))),
            B -> Expansion(Seq(Seq(x, B), Seq(y))),
            C -> Expansion(Seq(Seq(z, C), Seq(A)))))
    g.markovize_horizontal() should equal (
        Grammar(Seq(A, A, A),
            
        
    )
    
    
  }*/
}