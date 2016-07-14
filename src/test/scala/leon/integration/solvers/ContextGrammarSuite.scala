package leon
package integration.solvers

import synthesis.grammars.ContextGrammar
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
import org.scalatest.matchers.Matcher
import org.scalatest.matchers.MatchResult

trait CustomGrammarEqualMatcher[U, V] extends ContextGrammar[U, V] {
  def indexDifference(s1: String, s2: String): Int = {
    def rec(min: Int, max: Int): Int = if(max-min <= 1) min else {
      val mid = (min+max)/2
      val s1mid = s1.substring(0, mid)
      val s2mid = s2.substring(0, mid)
      if(s1mid != s2mid) rec(min, mid) else rec(mid, max)
    }
    rec(0, Math.min(s1.length, s2.length))
  }
  
  class EqualGrammarMatcher(expectedGrammar: Grammar) extends Matcher[Grammar] {
    def apply(left: Grammar) = {
      val leftString = grammarToString(left)
      val expected = grammarToString(expectedGrammar)
      val problem = indexDifference(leftString, expected)
      val msg1 = leftString.substring(0, problem) + "***got***" + leftString.substring(problem)
      val msg2 = expected.substring(0, problem) + "***expected***" + expected.substring(problem)
      MatchResult(
        left == expectedGrammar,
        s"$msg1\n ***did not equal*** \n$msg2",
        s"${grammarToString(left)}\n ***equaled*** \n${grammarToString(expectedGrammar)}"
      )
    }
  }

  def equalGrammar(grammar: Grammar) = new EqualGrammarMatcher(grammar)
}

class ContextGrammarString extends ContextGrammar[String, String] with CustomGrammarEqualMatcher[String, String]

/**
 * @author Mikael
 */
class ContextGrammarSuite extends FunSuite with Matchers with ScalaFutures {
  val ctx = new ContextGrammarString
  import ctx._
  
  val A = NonTerminal("A")
  val B = NonTerminal("B")
  val C = NonTerminal("C")
  val D = NonTerminal("D")
  val E = NonTerminal("E")
  val F = NonTerminal("F")
  val x = Terminal("x")("")
  val y = Terminal("y")("")
  val z = Terminal("z")("")
  val w = Terminal("w")("")
  
  test("Horizontal Markovization Simple")  {
    val xA = A.copy(hcontext = List(x))
    val xB = B.copy(hcontext = List(x))
    val xC = C.copy(hcontext = List(x))
    val xAA = A.copy(hcontext = List(x, A))
    val xAB = B.copy(hcontext = List(x, A))
    val xAC = C.copy(hcontext = List(x, A))
    val AA = A.copy(hcontext = List(A))
    val AB = B.copy(hcontext = List(A))
    val AC = C.copy(hcontext = List(A))
    
    val grammar1 = 
      Grammar(List(A, A), Map(A -> VerticalRHS(Seq(B, C)),
                           B -> HorizontalRHS(x, Seq(A, A)),
                           C -> HorizontalRHS(y, Nil)))

    val grammar2 =
      Grammar(List(A, AA), Map(A -> VerticalRHS(Seq(B, C)),
                               B -> HorizontalRHS(x, Seq(xA, xAA)),
                               C -> HorizontalRHS(y, Nil),
                               xA -> VerticalRHS(Seq(xB, xC)),
                               xB -> HorizontalRHS(x, Seq(xA, xAA)),
                               xC -> HorizontalRHS(y, Nil),
                               AA -> VerticalRHS(Seq(AB, AC)),
                               AB -> HorizontalRHS(x, Seq(xA, xAA)),
                               AC -> HorizontalRHS(y, Nil),
                               xAA -> VerticalRHS(Seq(xAB, xAC)),
                               xAB -> HorizontalRHS(x, Seq(xA, xAA)),
                               xAC -> HorizontalRHS(y, Nil)
                           ))
        
    grammar1.markovize_horizontal() should equalGrammar (grammar2)
  }
  
  test("Horizontal Markovization filtered")  {
    val BA = A.copy(hcontext = List(B))
    val AB = B.copy(hcontext = List(A))
    
    val grammar1 = 
      Grammar(List(A, B),
          Map(A -> Expansion(List(List(B, A), List(y))),
              B -> Expansion(List(List(x)))
              ))
    val grammar2 =
      Grammar(List(A, AB),
          Map(A -> Expansion(List(List(B, A), List(y))),
              B -> Expansion(List(List(x))),
              AB -> Expansion(List(List(x)))
              ))

    grammar1.markovize_horizontal_filtered(_.tag == "B", false) should equalGrammar (grammar2)
    grammar2.markovize_horizontal_filtered(_.tag == "B", false) should equalGrammar (grammar2)
  }
  
  test("Vertical Markovization simple") {
    val AA = A.copy(vcontext = List(A))
    val AAA = A.copy(vcontext = List(AA, A))
    val grammar1 = 
      Grammar(List(A), Map(A -> Expansion(List(List(x, A), List(y)))))
    val grammar2 =
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, AA), List(y))),
              AA -> Expansion(List(List(x, AA), List(y)))))
    val grammar3 =
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, AA), List(y))),
              AA -> Expansion(List(List(x, AAA), List(y))),
              AAA -> Expansion(List(List(x, AAA), List(y)))))
    
    grammar1.markovize_vertical() should equalGrammar (grammar2)
    grammar2.markovize_vertical() should equalGrammar (grammar3)
  }
  
  test("Vertical Markovization double") {
    val AA = A.copy(vcontext = List(A))
    val BA = A.copy(vcontext = List(B))
    val AB = B.copy(vcontext = List(A))
    val BB = B.copy(vcontext = List(B))
    
    val grammar1 = 
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, B), List(y))),
              B -> Expansion(List(List(z, A), List(x)))))

    val grammar2 =
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, AB), List(y))),
              BA -> Expansion(List(List(x, AB), List(y))),
              AB -> Expansion(List(List(z, BA), List(x)))))
    
    grammar1.markovize_vertical() should equalGrammar (grammar2)
  }
  
  test("Vertical Markovization triple") {
    val AA = A.copy(vcontext = List(A))
    val BA = A.copy(vcontext = List(B))
    val AB = B.copy(vcontext = List(A))
    val BB = B.copy(vcontext = List(B))
    
    val grammar1 = 
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, B), List(y))),
              B -> Expansion(List(List(z, A), List(z, B), List(x)))))

    val grammar2 =
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, AB), List(y))),
              BA -> Expansion(List(List(x, AB), List(y))),
              AB -> Expansion(List(List(z, BA), List(z, BB), List(x))),
              BB -> Expansion(List(List(z, BA), List(z, BB), List(x)))
          ))
          
    grammar1.markovize_vertical() should equalGrammar (grammar2)
  }
  
  // Extend the grammar by taking the unique vertical context of an abstract class, not directly vertical.
  // In this context: A -> A -> B -> B -> B -> A should remind only A -> B -> A
  test("Abstract vertical Markovization") {
    val Alist = NonTerminal("Alist")
    val Acons = NonTerminal("Acons")
    val Anil = NonTerminal("Anil")
    val acons = Terminal("acons")("")
    val anil = Terminal("anil")("")
    
    val Blist = NonTerminal("Blist")
    val Bcons = NonTerminal("Bcons")
    val Bnil = NonTerminal("Bnil")
    val bcons = Terminal("bcons")("")
    val bnil = Terminal("bnil")("")
    val grammar =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, Blist, Alist))),
              Anil -> Expansion(List(List(anil, x))),
              Blist -> Expansion(List(List(Bcons), List(Bnil))),
              Bcons -> Expansion(List(List(bcons, Alist, Blist))),
              Bnil -> Expansion(List(List(bnil, y)))))
    
    val AconsB = Acons.copy(vcontext = List(Blist))
    val AnilB = Anil.copy(vcontext = List(Blist))
    val AlistB = Alist.copy(vcontext = List(Blist))
    val AconsA = Acons.copy(vcontext = List(Alist))
    val AnilA = Anil.copy(vcontext = List(Alist))
    val AlistA = Alist.copy(vcontext = List(Alist))
    val BconsA = Bcons.copy(vcontext = List(Alist))
    val BnilA = Bnil.copy(vcontext = List(Alist))
    val BlistA = Blist.copy(vcontext = List(Alist))
    
    val grammar2 =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, BlistA, AlistA))),
              Anil -> Expansion(List(List(anil, x))),
              AlistA -> Expansion(List(List(AconsA), List(AnilA))),
              AconsA -> Expansion(List(List(acons, BlistA, AlistA))),
              AnilA -> Expansion(List(List(anil, x))),
              AlistB -> Expansion(List(List(AconsB), List(AnilB))),
              AconsB -> Expansion(List(List(acons, BlistA, AlistB))),
              AnilB -> Expansion(List(List(anil, x))),
              BlistA -> Expansion(List(List(BconsA), List(BnilA))),
              BconsA -> Expansion(List(List(bcons, AlistB, BlistA))),
              BnilA -> Expansion(List(List(bnil, y)))))
              
    grammar.markovize_abstract_vertical() should equalGrammar (grammar2)
  }
  
  // Extend the grammar by taking the unique vertical context of an abstract class, not directly vertical.
  // In this context: A -> A -> B -> B -> B -> A should remind only A -> B -> A
  test("Abstract vertical Markovization Filtered") {
    val Alist = NonTerminal("Alist")
    val Acons = NonTerminal("Acons")
    val Anil = NonTerminal("Anil")
    val acons = Terminal("acons")("")
    val anil = Terminal("anil")("")
    
    val Blist = NonTerminal("Blist")
    val Bcons = NonTerminal("Bcons")
    val Bnil = NonTerminal("Bnil")
    val bcons = Terminal("bcons")("")
    val bnil = Terminal("bnil")("")
    val grammar =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, Blist, Alist))),
              Anil -> Expansion(List(List(anil, x))),
              Blist -> Expansion(List(List(Bcons), List(Bnil))),
              Bcons -> Expansion(List(List(bcons, Alist, Blist))),
              Bnil -> Expansion(List(List(bnil, y)))))
    
    val BconsA = Bcons.copy(vcontext = List(Alist))
    val BconsB = Bcons.copy(vcontext = List(Blist))
    val BnilA = Bnil.copy(vcontext = List(Alist))
    val BnilB = Bnil.copy(vcontext = List(Blist))
    val BlistA = Blist.copy(vcontext = List(Alist))
    val BlistB = Blist.copy(vcontext = List(Blist))
    
    val grammar2 =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, BlistA, Alist))),
              Anil -> Expansion(List(List(anil, x))),
              BlistA -> Expansion(List(List(BconsA), List(BnilA))),
              BconsA -> Expansion(List(List(bcons, Alist, BlistA))),
              BnilA -> Expansion(List(List(bnil, y)))))
              
    grammar.markovize_abstract_vertical_filtered(_.tag == "Blist") should equalGrammar (grammar2)
  }
  
  test("Vertical Markovization on self structures") {
    val Alist = NonTerminal("Alist")
    val Acons = NonTerminal("Acons")
    val Anil = NonTerminal("Anil")
    val acons = Terminal("acons")("")
    val anil = Terminal("anil")("")
    val T = NonTerminal("T")
    val t = Terminal("t")("")
    
    val grammar =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, T, T, Alist))),
              Anil -> Expansion(List(List(anil, x))),
              T -> Expansion(List(List(t)))))
    
    val AconsA = Acons.copy(vcontext = List(Alist))
    val AlistA = Alist.copy(vcontext = List(Alist))
    val AnilA = Anil.copy(vcontext = List(Alist))
    
    val grammar2 =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, T, T, AlistA))),
              Anil -> Expansion(List(List(anil, x))),
              AlistA -> Expansion(List(List(AconsA), List(AnilA))),
              AconsA -> Expansion(List(List(acons, T, T, AlistA))),
              AnilA -> Expansion(List(List(anil, x))),
              T -> Expansion(List(List(t)))))
          
              
    grammar.markovize_abstract_vertical_filtered(_.tag == "Alist") should equalGrammar (grammar2)
  }
}