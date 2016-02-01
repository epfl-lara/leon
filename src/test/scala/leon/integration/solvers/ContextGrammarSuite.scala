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

trait CustomGrammarEqualMatcher[U, V, T <: ContextGrammar[U, V]] {
  def symbolToString(symbol: T#Symbol): String = {
    symbol match {
      case s: T#NonTerminal => nonterminalToString(s)
      case s: T#Terminal => terminalToString(s)
    }
  }
  def nonterminalToString(nonterminal: T#NonTerminal): String = {
    nonterminal.tag + (if(nonterminal.vcontext != Nil) "_v["+nonterminal.vcontext.map(x => symbolToString(x)).reduce(_ + "," + _) + "]" else "") +
    (if(nonterminal.hcontext != Nil) "_h["+nonterminal.hcontext.map(x => symbolToString(x)).reduce(_ + "," + _)+"]" else "")
  }
  def terminalToString(terminal: T#Terminal): String = {
    terminal.tag + (if(terminal.terminalTag == "") "" else "_" + terminal.terminalTag)
  }
  def reduce(l: Iterable[String], separator: String) = if(l == Nil) "" else l.reduce(_ + separator + _)
  def expansionToString(expansion: T#Expansion): String = {
    reduce(expansion.ls.map(l => reduce(l.map(x => symbolToString(x)), " ")), " | ")
  }
  
  def grammarToString(grammar: T#Grammar) = {
    "Start: " + reduce(grammar.start.map(s => symbolToString(s)), " | ") + "\n" +
    reduce(grammar.rules.map(kv => symbolToString(kv._1) + " -> " + expansionToString(kv._2)).toList.sorted, "\n")
  }
  
  class EqualGrammarMatcher(expectedGrammar: T#Grammar) extends Matcher[T#Grammar] {
    def apply(left: T#Grammar) = {
      MatchResult(
        left == expectedGrammar,
        s"${grammarToString(left)}\n ***did not equal*** \n${grammarToString(expectedGrammar)}",
        s"${grammarToString(left)}\n ***equaled*** \n${grammarToString(expectedGrammar)}"
      )
    }
  }

  def equalGrammar(grammar: T#Grammar) = new EqualGrammarMatcher(grammar)
}

class ContextGrammarString extends ContextGrammar[String, String] with CustomGrammarEqualMatcher[String, String, ContextGrammarString]

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
  val x = Terminal("x", "")
  val y = Terminal("y", "")
  val z = Terminal("z", "")
  val w = Terminal("w", "")
  
  test("Horizontal Markovization Simple")  {
    val xA = A.copy(hcontext = List(x))
    val grammar1 = 
      Grammar(Seq(A), Map(A -> Expansion(Seq(Seq(x, A), Seq(y)))))
    val grammar2 =
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, xA), Seq(y))),
              xA -> Expansion(Seq(Seq(x, xA), Seq(y)))))
        
    grammar1.markovize_horizontal() should equalGrammar (grammar2)
    grammar2.markovize_horizontal() should equalGrammar (grammar2)
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
              B -> Expansion(Seq(Seq(x))),
              AB -> Expansion(Seq(Seq(x))),
              BA -> Expansion(Seq(Seq(B, BA), Seq(y)))
              ))

    grammar1.markovize_horizontal() should equalGrammar (grammar2)
    grammar2.markovize_horizontal() should equalGrammar (grammar2)
  }
  
  test("Vertical Markovization simple") {
    val AA = A.copy(vcontext = List(A))
    val AAA = A.copy(vcontext = List(AA, A))
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
    
    grammar1.markovize_vertical() should equalGrammar (grammar2)
    grammar2.markovize_vertical() should equalGrammar (grammar3)
  }
  
  test("Vertical Markovization double") {
    val AA = A.copy(vcontext = List(A))
    val BA = A.copy(vcontext = List(B))
    val AB = B.copy(vcontext = List(A))
    val BB = B.copy(vcontext = List(B))
    
    val grammar1 = 
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, B), Seq(y))),
              B -> Expansion(Seq(Seq(z, A), Seq(x)))))

    val grammar2 =
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, AB), Seq(y))),
              BA -> Expansion(Seq(Seq(x, AB), Seq(y))),
              AB -> Expansion(Seq(Seq(z, BA), Seq(x)))))
    
    grammar1.markovize_vertical() should equal (grammar2)
  }
  
  test("Vertical Markovization triple") {
    val AA = A.copy(vcontext = List(A))
    val BA = A.copy(vcontext = List(B))
    val AB = B.copy(vcontext = List(A))
    val BB = B.copy(vcontext = List(B))
    
    val grammar1 = 
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, B), Seq(y))),
              B -> Expansion(Seq(Seq(z, A), Seq(z, B), Seq(x)))))

    val grammar2 =
      Grammar(Seq(A),
          Map(A -> Expansion(Seq(Seq(x, AB), Seq(y))),
              BA -> Expansion(Seq(Seq(x, AB), Seq(y))),
              AB -> Expansion(Seq(Seq(z, BA), Seq(z, BB), Seq(x))),
              BB -> Expansion(Seq(Seq(z, BA), Seq(z, BB), Seq(x)))
          ))
          
    grammar1.markovize_vertical() should equal (grammar2)
  }
  
  // Extend the grammar by taking the unique vertical context of an abstract class, not directly vertical.
  // In this context: A -> A -> B -> B -> B -> A should remind only A -> B -> A
  test("Abstract vertical Markovization") {
    val Alist = NonTerminal("Alist")
    val Acons = NonTerminal("Acons")
    val Anil = NonTerminal("Anil")
    val acons = Terminal("acons", "")
    val anil = Terminal("anil", "")
    
    val Blist = NonTerminal("Blist")
    val Bcons = NonTerminal("Bcons")
    val Bnil = NonTerminal("Bnil")
    val bcons = Terminal("bcons", "")
    val bnil = Terminal("bnil", "")
    val grammar =
      Grammar(Seq(Alist),
          Map(Alist -> Expansion(Seq(Seq(Acons), Seq(Anil))),
              Acons -> Expansion(Seq(Seq(acons, Blist, Alist))),
              Anil -> Expansion(Seq(Seq(anil, x))),
              Blist -> Expansion(Seq(Seq(Bcons), Seq(Bnil))),
              Bcons -> Expansion(Seq(Seq(bcons, Alist, Blist))),
              Bnil -> Expansion(Seq(Seq(bnil, y)))))
    
    val AconsB = Acons.copy(vcontext = List(Blist))
    val AnilB = Anil.copy(vcontext = List(Blist))
    val AlistB = Alist.copy(vcontext = List(Blist))
    val BconsA = Bcons.copy(vcontext = List(Alist))
    val BnilA = Bnil.copy(vcontext = List(Alist))
    val BlistA = Blist.copy(vcontext = List(Alist))
    
    val grammar2 =
      Grammar(Seq(Alist),
          Map(Alist -> Expansion(Seq(Seq(Acons), Seq(Anil))),
              Acons -> Expansion(Seq(Seq(acons, BlistA, Alist))),
              Anil -> Expansion(Seq(Seq(anil, x))),
              AlistB -> Expansion(Seq(Seq(AconsB), Seq(AnilB))),
              AconsB -> Expansion(Seq(Seq(acons, BlistA, AlistB))),
              AnilB -> Expansion(Seq(Seq(anil, x))),
              BlistA -> Expansion(Seq(Seq(BconsA), Seq(BnilA))),
              BconsA -> Expansion(Seq(Seq(bcons, AlistB, BlistA))),
              BnilA -> Expansion(Seq(Seq(bnil, y)))))
              
    grammar.markovize_abstract_vertical() should equalGrammar (grammar2)
  }
}