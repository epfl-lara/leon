package leon
package synthesis
package grammars

import scala.collection.mutable.ListBuffer

class ContextGrammar[SymbolTag, TerminalTag] {
  /** A tagged symbol */
  abstract class Symbol { def tag: SymbolTag }
  /** A tagged non-terminal */
  case class NonTerminal(tag: SymbolTag, vcontext: List[NonTerminal] = Nil, hcontext: List[Symbol] = Nil) extends Symbol
  /** A tagged terminal */
  case class Terminal(tag: SymbolTag, terminalTag: TerminalTag) extends Symbol
  
  /** All possible right-hand-side of rules */
  case class Expansion(ls: Seq[Seq[Symbol]]) {
    def symbols = ls.flatten
    def ++(other: Expansion): Expansion = Expansion((ls ++ other.ls).distinct)
    def ++(other: Option[Expansion]): Expansion = other match {case Some(e) => this ++ e case None => this }
    def contains(s: Symbol): Boolean = {
      ls.exists { l => l.exists { x => x == s } }
    }
    /** Maps symbols to other symbols */
    def map(f: Symbol => Symbol): Expansion = {
      Expansion(ls.map(_.map(f)))
    }
    /** Maps symbols with the left context as second argument */
    def mapLeftContext(f: (Symbol, List[Symbol]) => Symbol): Expansion = {
      Expansion(ls.map(l => (l.foldLeft(ListBuffer[Symbol]()){
        case (l: ListBuffer[Symbol], s: Symbol) => l += f(s, l.toList)
      }).toList ))
    }
  }
  
  // Shortcuts and helpers.
  
  /** An expansion which has only 1 symbol for each right-hand sie */
  object VerticalRHS{
    def apply(symbols: Seq[NonTerminal]) = Expansion(symbols.map(symbol => Seq(symbol)))
    def unapply(e: Expansion): Option[Seq[NonTerminal]] =
      if(e.ls.forall(rhs => rhs.length == 1 && rhs.head.isInstanceOf[NonTerminal]))
        Some(e.ls.map(rhs => rhs.head.asInstanceOf[NonTerminal]))
      else None
  }
  /** An expansion which has only 1 right-hand-side with as many symbols as possible */
  object HorizontalRHS {
    def apply(symbols: Seq[NonTerminal]) = Expansion(Seq(symbols))
    def unapply(e: Expansion): Option[Seq[NonTerminal]] = e.ls match {
      case Seq(symbols) if symbols.forall { x => x.isInstanceOf[NonTerminal] } => Some(symbols.map(_.asInstanceOf[NonTerminal]))
      case _ => None
    }
  }
  /** An expansion which has only 1 terminal and only 1 right-hand-side */
  object TerminalRHS {
    def apply(t: Terminal) = Expansion(Seq(Seq(t)))
    def unapply(e: Expansion): Option[Terminal] = e.ls match {
      case Seq(Seq(t: Terminal)) => Some(t)
      case _ => None
    }
  }
  
  /** A grammar here has a start sequence instead of a start symbol */
  case class Grammar(start: Seq[Symbol], rules: Map[NonTerminal, Expansion]) {
    /** Returns all non-terminals of the given grammar */
    def nonTerminals: Seq[NonTerminal] = {
      (start.collect{ case k: NonTerminal => k } ++
          (for{(lhs, rhs) <- rules; s <- Seq(lhs) ++
          (for(r <- rhs.symbols.collect{ case k: NonTerminal => k }) yield r)} yield s)).distinct
    }
    
    
    /** Applies 1-markovization to the grammar (add 1 history to every node) */
    def markovize_vertical(): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      def parents(nt: NonTerminal): Seq[NonTerminal] = {
        rulesSeq.collect{ case (ntprev, expansion)  if expansion.contains(nt) => ntprev }
      }
      var mapping = Map[NonTerminal, List[NonTerminal]](start.collect{case x: NonTerminal => x }.map(x => x -> List(x)) : _*)
      def updateMapping(nt: NonTerminal, topContext: List[NonTerminal]): NonTerminal = {
        val res = nt.copy(vcontext = topContext)
        mapping += nt -> (res::mapping.getOrElse(nt, Nil)).distinct
        res
      }
      
      val newRules = (for{
        nt <- nts
        expansion = rules(nt)
      }  yield (nt -> (expansion.map{(s: Symbol) => s match {
        case n@NonTerminal(tag, vc, hc) => updateMapping(n, nt::nt.vcontext)
        case e => e
      }}))).toMap
      
      val newRules2 = 
        for{(nt, expansion) <- newRules
            nnt <- mapping.getOrElse(nt, List(nt))
        } yield {
          nnt -> expansion
        }
      Grammar(start, newRules2)
    }
    
    /** Applies horizontal markovization to the grammar (add the left history to every node and duplicate rules as needed.
      * Is idempotent. */
    def markovize_horizontal(): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      def newHorizontalContexts(parents: Seq[NonTerminal], vContext: List[NonTerminal]): Seq[List[NonTerminal]] = {
        if(parents.nonEmpty) for(pnt <- parents) yield (pnt :: vContext)
        else List(vContext)
      }
      
      // Conversion from old to new non-terminals to duplicate rules afterwards.
      var mapping = Map[NonTerminal, List[NonTerminal]]()
      
      def updateMapping(nt: NonTerminal, leftContext: List[Symbol]): NonTerminal = {
        val res = nt.copy(hcontext = leftContext)
        mapping += nt -> (res::mapping.getOrElse(nt, Nil)).distinct
        res
      }
      
      /** Add to each symbol its left context */
      def processSequence(sq: Seq[Symbol]): Seq[Symbol] = {
        sq.foldLeft(List[Symbol]()) {
          case (leftContext, nt@NonTerminal(tag, vc, Nil)) =>
            leftContext :+ updateMapping(nt, leftContext)
          case (leftContext, e) => leftContext :+ e
        }
      }
      val newStart = processSequence(start)
      // Add the context to each symbol in each rule.
      val newRules =
        for{nt <- nts} yield {
          val expansion = rules(nt)
          nt -> expansion.mapLeftContext{ (s: Symbol, l: List[Symbol]) =>
            s match {
              case nt@NonTerminal(tag, vc, Nil) => updateMapping(nt, l)
              case e => e
            }
          }
        }
      val newRules2 =
        for{(nt, expansion) <- newRules
            nnt <- mapping.getOrElse(nt, List(nt))
        } yield {
          nnt -> expansion
        }
      Grammar(newStart, newRules2.toMap)
    }
    
    def markovize_abstract_vertical(): Grammar = {
      this
    }
    
  }
}