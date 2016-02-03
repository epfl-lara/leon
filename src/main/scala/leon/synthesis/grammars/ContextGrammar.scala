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
      (startNonTerminals ++
          (for{(lhs, rhs) <- rules; s <- Seq(lhs) ++
          (for(r <- rhs.symbols.collect{ case k: NonTerminal => k }) yield r)} yield s)).distinct
    }
    lazy val startNonTerminals: Seq[NonTerminal] = {
      start.collect{ case k: NonTerminal => k }
    }

    abstract class NonTerminalMapping {
      // Conversion from old to new non-terminals to duplicate rules afterwards.
      private lazy val originalMapping = Map[NonTerminal, List[NonTerminal]](startNonTerminals.map(x => x -> List(x)) : _*)
      protected var mapping = originalMapping
      // Resets the mapping transformation
      def reset() = mapping = originalMapping
        
      def apply(lhs: NonTerminal): Seq[NonTerminal]
      
        // Keeps expansion the same but applies the current mapping to all keys
      def mapKeys(rules: Map[NonTerminal, Expansion]) = 
        for{(lhs, expansion) <- rules
          new_lhs <- apply(lhs)
        } yield {
          new_lhs -> expansion
        }
    }

    /** Applies 1-markovization to the grammar (add 1 history to every node) */
    def markovize_vertical(): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      def parents(nt: NonTerminal): Seq[NonTerminal] = {
        rulesSeq.collect{ case (ntprev, expansion)  if expansion.contains(nt) => ntprev }
      }
      object Mapping extends NonTerminalMapping {
        mapping = Map[NonTerminal, List[NonTerminal]](startNonTerminals.map(x => x -> List(x)) : _*)
        def updateMapping(nt: NonTerminal, topContext: List[NonTerminal]): NonTerminal = {
          val res = nt.copy(vcontext = topContext)
          mapping += nt -> (res::mapping.getOrElse(nt, Nil)).distinct
          res
        }
        def apply(elem: NonTerminal) = mapping.getOrElse(elem, List(elem))
      }
      
      val newRules = (for{
        nt <- nts
        expansion = rules(nt)
      }  yield (nt -> (expansion.map{(s: Symbol) => s match {
        case n@NonTerminal(tag, vc, hc) => Mapping.updateMapping(n, nt::nt.vcontext)
        case e => e
      }}))).toMap
      
      val newRules2 = Mapping.mapKeys(newRules)
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
      
      object Mapping extends NonTerminalMapping {
        def updateMapping(nt: NonTerminal, leftContext: List[Symbol]): NonTerminal = {
          val res = nt.copy(hcontext = leftContext)
          mapping += nt -> (res::mapping.getOrElse(nt, Nil)).distinct
          res
        }
        
        def apply(elem: NonTerminal) = mapping.getOrElse(elem, List(elem))
      }
      
      /** Add to each symbol its left context */
      def processSequence(sq: Seq[Symbol]): Seq[Symbol] = {
        sq.foldLeft(List[Symbol]()) {
          case (leftContext, nt@NonTerminal(tag, vc, Nil)) =>
            leftContext :+ Mapping.updateMapping(nt, leftContext)
          case (leftContext, e) => leftContext :+ e
        }
      }
      val newStart = processSequence(start)
      // Add the context to each symbol in each rule.
      val newRules =
        (for{nt <- nts} yield {
          val expansion = rules(nt)
          nt -> expansion.mapLeftContext{ (s: Symbol, l: List[Symbol]) =>
            s match {
              case nt@NonTerminal(tag, vc, Nil) => Mapping.updateMapping(nt, l)
              case e => e
            }
          }
        }).toMap
      val newRules2 =Mapping.mapKeys(newRules)
      Grammar(newStart, newRules2.toMap)
    }
    
    /** Same as vertical markovization, but we add in the vertical context only the nodes coming from a "different abstract hierarchy"
      * Different abstract hierarchy means that nodes do not have the same ancestor.
      */
    def markovize_abstract_vertical(): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      def parents(nt: NonTerminal): Seq[NonTerminal] = {
        rulesSeq.collect{ case (ntprev, expansion)  if expansion.contains(nt) => ntprev }
      }
      // Utilities to perform the mapping from one non-terminal to many new non-terminals
      object Mapping extends NonTerminalMapping {
        // Adds a new mapping by introducing a top-context.
        def updateTopContext(nt: NonTerminal, topContext: List[NonTerminal]): NonTerminal = {
          val new_nt = nt.copy(vcontext = topContext)
          mapping += nt -> (new_nt::mapping.getOrElse(nt, Nil)).distinct
          Original.recordMapping(nt, new_nt)
          new_nt
        }
        // Returns the list of new non-terminals which will replace the given nonterminal
        def apply(elem: NonTerminal) = 
          (if(Ancestor.isInStart(elem))
                List(elem)
              else Nil) ++
             mapping.getOrElse(elem, List(elem))
      }
      
      // An object to keep track of all modifications to return to the original symbols.
      // Useful to find "ancestors"
      object Original {
        private var originals = Map[NonTerminal, NonTerminal]()
        def recordMapping(nt: NonTerminal, new_nt: NonTerminal): Unit = {
          originals += new_nt -> originals.getOrElse(nt, nt)
        }
        def apply(nt: NonTerminal) = originals.getOrElse(nt, nt)
      }
      
      // An ancestor of a non-terminal is the non-terminal which can produce it only and cannot be produced itself.
      object Ancestor {
        private var mappingAncestor = Map[NonTerminal, NonTerminal]()
        private def find(nt: NonTerminal): NonTerminal = {
          Grammar.this.rules.find(kv => {
            kv._2.ls.exists(rhs => rhs.size == 1 && rhs(0) == nt)
          }) match {
            case None => nt
            case Some(kv) => apply(kv._1)
          }
        }
        /** Finds and cache the ancestor in a dynamic way */
        def apply(nt: NonTerminal): NonTerminal = {
          mappingAncestor.getOrElse(nt, {
            val a = find(nt)
            mappingAncestor += nt -> a
            a
          })
        }
        // Returns true if two terminals share a common ancestor
        def haveCommonType(nt1: NonTerminal, nt2: NonTerminal): Boolean = {
          apply(nt1) == apply(nt2)
        }
        // Returns true if the ancestor of this non-terminal is present in the start non-terminals.
        def isInStart(lhs: NonTerminal) = {
          val ancestor_lhs = Ancestor(lhs)
          startNonTerminals.exists(startnt => startnt == ancestor_lhs)
        }
      }
      
      // If nt is not already in the hierarchy of the first element of v (or n if v is empty), add to it. Else discard it.
      def mergeContexts(lhs: NonTerminal, rhsterm: NonTerminal): List[NonTerminal] = {
        lhs.vcontext match {
          case Nil => if(Ancestor.haveCommonType(lhs, rhsterm)) Nil else Ancestor(lhs)::Nil
          case vhead::vtail => if(Ancestor.haveCommonType(lhs, vhead)) lhs.vcontext else Ancestor(lhs)::lhs.vcontext
        }
      }
      
      val newRules = (for{
        lhs <- nts
        expansion = rules(lhs)
      }  yield (lhs -> (expansion.map{(s: Symbol) => s match {
        case rhsterm@NonTerminal(tag, vc, hc) => Mapping.updateTopContext(rhsterm, mergeContexts(lhs, rhsterm))
        case e => e
      }}))).toMap
      
      val newRules2 = Mapping.mapKeys(newRules)
      val newRules3 = leon.utils.fixpoint({(newRules: Map[NonTerminal, Expansion]) => 
        Mapping.reset()
        val newRules4 = for{(lhs, expansion) <- newRules} yield {
          lhs -> expansion.map{ (s: Symbol) => s match {
            case rhsterm@NonTerminal(tag, vc, hc) => 
              val lhs_original = Original(lhs)
              val rhs_original = Original(rhsterm)
              if (Ancestor.haveCommonType(rhs_original, lhs_original) &&
                  rhsterm.vcontext != lhs.vcontext) {
                Mapping.updateTopContext(rhsterm, lhs.vcontext)
              } else rhsterm
            case e => e
            }
          }
        }
        Mapping.mapKeys(newRules4)
      }, 64)(newRules2) // 64 is the maximum number of nested hierarchies it supports.
      
      Grammar(start, newRules3)
    }
    
  }
}