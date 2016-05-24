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

trait CustomGrammarEqualMatcher[U, V, W, T <: ContextGrammar[U, V, W]] {
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
    "Start: " + reduce(grammar.start.map(s => symbolToString(s)), " ") + "\n" +
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

class ContextGrammarString extends ContextGrammar[String, String, String] with CustomGrammarEqualMatcher[String, String, String, ContextGrammarString]

/**
 * @author Mikael
 */
class ContextGrammarSuite extends FunSuite with Matchers with ScalaFutures {
  val ctx = new ContextGrammarString
  import ctx._
  
  val A = NonTerminal("A", "")
  val B = NonTerminal("B", "")
  val C = NonTerminal("C", "")
  val D = NonTerminal("D", "")
  val E = NonTerminal("E", "")
  val F = NonTerminal("F", "")
  val x = Terminal("x", "")
  val y = Terminal("y", "")
  val z = Terminal("z", "")
  val w = Terminal("w", "")
  
  test("Horizontal Markovization Simple")  {
    val xA = A.copy(hcontext = List(x))
    val grammar1 = 
      Grammar(List(A), Map(A -> Expansion(List(List(x, A), List(y)))))
    val grammar2 =
      Grammar(List(A),
          Map(A -> Expansion(List(List(x, xA), List(y))),
              xA -> Expansion(List(List(x, xA), List(y)))))
        
    grammar1.markovize_horizontal() should equalGrammar (grammar2)
    grammar2.markovize_horizontal() should equalGrammar (grammar2)
  }
  test("Horizontal Markovization Double")  {
    val BA = A.copy(hcontext = List(B))
    val AB = B.copy(hcontext = List(A))
    
    val grammar1 = 
      Grammar(List(A, B),
          Map(A -> Expansion(List(List(B, A), List(y))),
              B -> Expansion(List(List(x)))
              ))
    val grammar2 =
      Grammar(List(A, AB),
          Map(A -> Expansion(List(List(B, BA), List(y))),
              B -> Expansion(List(List(x))),
              AB -> Expansion(List(List(x))),
              BA -> Expansion(List(List(B, BA), List(y)))
              ))

    grammar1.markovize_horizontal() should equalGrammar (grammar2)
    grammar2.markovize_horizontal() should equalGrammar (grammar2)
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

    grammar1.markovize_horizontal_filtered(_.tag == "B") should equalGrammar (grammar2)
    grammar2.markovize_horizontal_filtered(_.tag == "B") should equalGrammar (grammar2)
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
    
    grammar1.markovize_vertical() should equal (grammar2)
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
          
    grammar1.markovize_vertical() should equal (grammar2)
  }
  
  // Extend the grammar by taking the unique vertical context of an abstract class, not directly vertical.
  // In this context: A -> A -> B -> B -> B -> A should remind only A -> B -> A
  test("Abstract vertical Markovization") {
    val Alist = NonTerminal("Alist", "")
    val Acons = NonTerminal("Acons", "")
    val Anil = NonTerminal("Anil", "")
    val acons = Terminal("acons", "")
    val anil = Terminal("anil", "")
    
    val Blist = NonTerminal("Blist", "")
    val Bcons = NonTerminal("Bcons", "")
    val Bnil = NonTerminal("Bnil", "")
    val bcons = Terminal("bcons", "")
    val bnil = Terminal("bnil", "")
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
    val BconsA = Bcons.copy(vcontext = List(Alist))
    val BnilA = Bnil.copy(vcontext = List(Alist))
    val BlistA = Blist.copy(vcontext = List(Alist))
    
    val grammar2 =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, BlistA, Alist))),
              Anil -> Expansion(List(List(anil, x))),
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
    val Alist = NonTerminal("Alist", "")
    val Acons = NonTerminal("Acons", "")
    val Anil = NonTerminal("Anil", "")
    val acons = Terminal("acons", "")
    val anil = Terminal("anil", "")
    
    val Blist = NonTerminal("Blist", "")
    val Bcons = NonTerminal("Bcons", "")
    val Bnil = NonTerminal("Bnil", "")
    val bcons = Terminal("bcons", "")
    val bnil = Terminal("bnil", "")
    val grammar =
      Grammar(List(Alist),
          Map(Alist -> Expansion(List(List(Acons), List(Anil))),
              Acons -> Expansion(List(List(acons, Blist, Alist))),
              Anil -> Expansion(List(List(anil, x))),
              Blist -> Expansion(List(List(Bcons), List(Bnil))),
              Bcons -> Expansion(List(List(bcons, Alist, Blist))),
              Bnil -> Expansion(List(List(bnil, y)))))
    
    val BconsA = Bcons.copy(vcontext = List(Alist))
    val BnilA = Bnil.copy(vcontext = List(Alist))
    val BlistA = Blist.copy(vcontext = List(Alist))
    
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
}