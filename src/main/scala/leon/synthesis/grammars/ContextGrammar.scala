package leon
package synthesis
package grammars

import scala.collection.mutable.ListBuffer

class ContextGrammar[SymbolTag, TerminalData] {
  /** A tagged symbol */
  abstract class Symbol { def tag: SymbolTag }
  /** A tagged non-terminal */
  case class NonTerminal(tag: SymbolTag, vcontext: List[NonTerminal] = Nil, hcontext: List[Symbol] = Nil) extends Symbol
  /** A tagged terminal */
  case class Terminal(tag: SymbolTag)(val terminalData: TerminalData) extends Symbol
  
  /** All possible right-hand-side of rules */
  case class Expansion(ls: List[List[Symbol]]) {
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
  
  /** An expansion which has only 1 non-terminal for each right-hand side */
  object VerticalRHS{
    def apply(symbols: Seq[NonTerminal]) = Expansion(symbols.map(symbol => List(symbol)).toList)
    def unapply(e: Expansion): Option[List[NonTerminal]] =
      if(e.ls.size >= 1 && e.ls.forall(rhs => rhs.length == 1 && rhs.head.isInstanceOf[NonTerminal]))
        Some(e.ls.map(rhs => rhs.head.asInstanceOf[NonTerminal]))
      else None
  }
  /** An expansion which has only 1 right-hand-side with one terminal and non-terminals */
  object HorizontalRHS {
    def apply(tag: Terminal, symbols: Seq[NonTerminal]) = Expansion(List(tag :: symbols.toList))
    def unapply(e: Expansion): Option[(Terminal, List[NonTerminal])] = e.ls match {
      case List((t: Terminal)::(nts : List[_])) 
        if nts.forall(_.isInstanceOf[NonTerminal]) =>
        Some((t, nts.map(_.asInstanceOf[NonTerminal])))
      case _ => None
    }
  }
  /** An expansion which has only 1 terminal and only 1 right-hand-side */
  object TerminalRHS {
    def apply(t: Terminal) = HorizontalRHS(t, Nil)
    def unapply(e: Expansion): Option[Terminal] = e.ls match {
      case List(List(t: Terminal)) => Some(t)
      case _ => None
    }
  }
  
  object AugmentedTerminalsRHS {
    def apply(t: Seq[Terminal], e: Expansion) = Expansion(t map (x => List(x: Symbol)) toList) ++ e
    def unapply(e: Expansion): Option[(List[Terminal], Expansion)] = e.ls match {
      case Nil => None
      case _::Nil => Some((Nil, e))
      case head::tail =>
        (head, unapply(Expansion(tail))) match {
          case (_, None) => None
          case (List(t: Terminal), Some((ts, exp))) => Some((t::ts, exp))
          case (lnt@List(nt: NonTerminal), Some((Nil, exp))) => Some((Nil, Expansion(List(lnt)) ++ exp))
          case _ => None
        }
    }
  }
  
  // Remove unreachable non-terminals
  def clean(g: Grammar): Grammar = {
    val reachable = leon.utils.fixpoint({
      (nt: Set[NonTerminal]) =>
        nt ++ (nt map (g.rules) flatMap (_.symbols) collect { case nt: NonTerminal => nt })
    }, 64)(g.startNonTerminals.toSet)
    val nonReachable = g.nonTerminals.toSet -- reachable
    g.copy(rules = g.rules -- nonReachable)
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
        
      def apply(elem: NonTerminal): Seq[NonTerminal] = mapping.getOrElse(elem, List(elem))
      
      def maybeKeep(elem: NonTerminal): Seq[NonTerminal] = Nil
        // Keeps expansion the same but applies the current mapping to all keys, creating only updates.
      def mapKeys(rules: Map[NonTerminal, Expansion]) = {
        val tmpRes2 = for{(lhs, expansion) <- rules.toSeq
          new_lhs <- (maybeKeep(lhs) ++ mapping.getOrElse(lhs, Nil)).distinct
        } yield {
          lhs -> (new_lhs -> expansion)
        }
        val rulestmpRes2 = rules -- tmpRes2.map(_._1) 
        rulestmpRes2 ++ tmpRes2.map(_._2)
      }
    }
    
    def markovize_vertical_filtered(pred: NonTerminal => Boolean): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      def parents(nt: NonTerminal): Seq[NonTerminal] = {
        rulesSeq.collect{ case (ntprev, expansion)  if expansion.contains(nt) => ntprev }
      }
      object Mapping extends NonTerminalMapping {
        mapping = Map[NonTerminal, List[NonTerminal]](startNonTerminals.map(x => x -> List(x)) : _*)
        def updateMapping(nt: NonTerminal, topContext: List[NonTerminal]): NonTerminal = {
          if(pred(nt)) {
            val res = nt.copy(vcontext = topContext)
            mapping += nt -> (res::mapping.getOrElse(nt, Nil)).distinct
            res
          } else nt
        }
      }
      
      val newRules = (for{
        nt <- nts
        expansion = rules(nt)
      }  yield (nt -> (expansion.map{(s: Symbol) => s match {
        case n:NonTerminal => Mapping.updateMapping(n, nt::nt.vcontext)
        case e => e
      }}))).toMap
      
      val newRules2 = Mapping.mapKeys(newRules)
      Grammar(start, newRules2)
    }

    /** Applies 1-markovization to the grammar (add 1 history to every node) */
    def markovize_vertical(): Grammar = {
      markovize_vertical_filtered(_ => true)
    }
    
    /** Perform horizontal markovization only on the provided non-terminals. */
    def markovize_horizontal_filtered(pred: NonTerminal => Boolean): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      def newHorizontalContexts(parents: Seq[NonTerminal], vContext: List[NonTerminal]): Seq[List[NonTerminal]] = {
        if(parents.nonEmpty) for(pnt <- parents) yield (pnt :: vContext)
        else List(vContext)
      }
      
      object Mapping extends NonTerminalMapping {
        def updateMapping(nt: NonTerminal, leftContext: List[Symbol]): NonTerminal = {
          if(pred(nt)) {
            val res = nt.copy(hcontext = leftContext)
            mapping += nt -> (res::mapping.getOrElse(nt, Nil)).distinct
            res
          } else nt
        }
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
    
    /** Applies horizontal markovization to the grammar (add the left history to every node and duplicate rules as needed.
      * Is idempotent. */
    def markovize_horizontal(): Grammar = {
      markovize_horizontal_filtered(_ => true)
    }
    
    /** Same as vertical markovization, but we add in the vertical context only the nodes coming from a "different abstract hierarchy". Top-level nodes count as a different hierarchy.
      * Different abstract hierarchy means that nodes do not have the same ancestor.
      * @param pred The top-most non-terminals to consider (i.e. abstract ones)
      */
    def markovize_abstract_vertical_filtered(pred: NonTerminal => Boolean): Grammar = {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      val ants = (nts filter { nt => // Abstract non terminals
        rules(nt) match {
          case AugmentedTerminalsRHS(terminals, VerticalRHS(sons)) => pred(nt)
          case _ => false
        }
      }).toSet
      val cnts = (nts filter { nt => // case class non terminals
        rules(nt) match {
          case AugmentedTerminalsRHS(terminals, HorizontalRHS(t, sons)) => true
          case _ => false
        }
      }).toSet
      var getAnts = Map[NonTerminal, NonTerminal]()
      nts foreach { nt =>
        rules(nt) match {
          case AugmentedTerminalsRHS(terminals, VerticalRHS(sons)) => sons.foreach(son => getAnts += son -> nt)
          case _ => false
        }
      }
      def getTopmostANT(nt: NonTerminal): NonTerminal = if(getAnts contains(nt)) getTopmostANT(getAnts(nt)) else nt
      def getAncestors(nt: NonTerminal): Set[NonTerminal] = getAnts.get(nt).map(getAncestors).getOrElse(Set.empty[NonTerminal]) + nt
      val startANT = startNonTerminals.map(getTopmostANT).toSet
      
      var toDuplicate = Map[NonTerminal, Set[NonTerminal]]()
      for(t <- startNonTerminals) {
        val topAnt = getTopmostANT(t)
        toDuplicate += topAnt -> Set(topAnt)
      }
      val newRules = rules.map{ case (k, expansion) =>
        k -> expansion.map{
          case nt: NonTerminal => 
            if(ants(nt)) {
              val antp = getTopmostANT(k)
              val ancestors = getAncestors(nt)
              val ancestorTop = getTopmostANT(nt)
              if(antp == ancestorTop && !startANT(antp)) nt else {
                for(ancestor <- ancestors) {
                  val ancestorCopy = ancestor.copy(vcontext = List(antp))
                  getAnts += ancestorCopy -> ancestor
                  toDuplicate += ancestor -> (toDuplicate.getOrElse(ancestor, Set()) + ancestorCopy)
                }
                nt.copy(vcontext = List(antp))
              }
            } else nt
          case s => s
        }
      }
      val newRules2 = for{
          (k, v) <- newRules
          kp <- (toDuplicate.getOrElse(k, Set(k)) + k)
      } yield {
        kp -> v
      }
      //println("newRules2 = " + grammarToString(Grammar(start, newRules2)))
      
      def reportVContext(nt: NonTerminal, parentNt: NonTerminal, rules: Map[NonTerminal, Expansion]): NonTerminal = {
        if((nt.vcontext.isEmpty || (getTopmostANT(parentNt) == getTopmostANT(nt) && parentNt.vcontext.nonEmpty)) && pred(getTopmostANT(nt))) {
          val thecopy = nt.copy(vcontext = parentNt.vcontext)
          if(!(rules contains thecopy)) {
            getAnts += thecopy -> nt
            toDuplicate += nt -> (toDuplicate.getOrElse(nt, Set()) + nt + thecopy)
          }
          thecopy
        } else nt
      }
      val newRules3 = leon.utils.fixpoint((newRules: Map[NonTerminal, Expansion]) => {
        toDuplicate = Map()
        val  res = for{
        (k, v) <- newRules
      } yield {
        v match {
          case AugmentedTerminalsRHS(terminals, VerticalRHS(children)) =>
            k -> AugmentedTerminalsRHS(terminals, VerticalRHS(children.map(x => reportVContext(x, k, newRules))))
          case AugmentedTerminalsRHS(terminals, HorizontalRHS(t, children)) =>
            k -> AugmentedTerminalsRHS(terminals, HorizontalRHS(t, children.map(x => reportVContext(x, k, newRules))))
          case _ => k -> v
        }
      }
      //println("newRules3 = " + grammarToString(Grammar(start, res)))
      //println("toDuplicate = " + toDuplicate.map{ case (k, v) => symbolToString(k) + "->" + v.map(symbolToString)})
      val res2 = for{
          (k, v) <- res
          kp <- toDuplicate.getOrElse(k, Set(k))
      } yield {
        kp -> v
      }
      //println("newRules4 = " + grammarToString(Grammar(start, res2)))
      res2}, 64)(newRules2)
      
      clean(Grammar(start, newRules3))
    }
    
    /** Same as vertical markovization, but we add in the vertical context only the nodes coming from a "different abstract hierarchy"
      * Different abstract hierarchy means that nodes do not have the same ancestor.
      */
    def markovize_abstract_vertical(): Grammar = {
      markovize_abstract_vertical_filtered(_ => true)
    }
    
  }
  
  def symbolToString(symbol: Symbol): String = {
    symbol match {
      case s: NonTerminal => nonterminalToString(s)
      case s: Terminal => terminalToString(s)
    }
  }
  def nonterminalToString(nonterminal: NonTerminal): String = {
    nonterminal.tag + (if(nonterminal.vcontext != Nil) "_v["+nonterminal.vcontext.map(x => symbolToString(x)).reduce(_ + "," + _) + "]" else "") +
    (if(nonterminal.hcontext != Nil) "_h["+nonterminal.hcontext.map(x => symbolToString(x)).reduce(_ + "," + _)+"]" else "")
  }
  def terminalToString(terminal: Terminal): String = {
    terminal.tag + (if(terminal.terminalData == "") "" else "_" + terminal.terminalData)
  }
  def reduce(l: Iterable[String], separator: String) = if(l == Nil) "" else l.reduce(_ + separator + _)
  def expansionToString(expansion: Expansion): String = {
    reduce(expansion.ls.map(l => reduce(l.map(x => symbolToString(x)), " ")), " | ")
  }
  
  def grammarToString(grammar: Grammar) = {
    "Start: " + reduce(grammar.start.map(s => symbolToString(s)), " ") + "\n" +
    reduce(grammar.rules.map(kv => symbolToString(kv._1) + " -> " + expansionToString(kv._2)).toList.sorted, "\n")
  }
}