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
  
  /** An expansion which starts with terminals and ends with something like HorizontalRHS or VerticalRHS */
  object AugmentedTerminalsRHS {
    def apply(t: Seq[Terminal], e: Expansion) = Expansion(t.map (x => List(x: Symbol)).toList) ++ e
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
    val res = g.copy(rules = g.rules -- nonReachable)
    res
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
    
    class MarkovizationContext(pred: NonTerminal => Boolean) {
      val nts = nonTerminals
      val rulesSeq = rules.toSeq
      /** Set of abstract non-terminals */
      val ants = (nts filter { nt => 
        rules(nt) match {
          case AugmentedTerminalsRHS(terminals, VerticalRHS(sons)) => pred(nt)
          case _ => false
        }
      }).toSet
      /** Set of case class non-terminals */
      val cnts = (nts filter { nt => // case class non terminals
        rules(nt) match {
          case AugmentedTerminalsRHS(terminals, HorizontalRHS(t, sons)) => true
          case _ => false
        }
      }).toSet
      var getAnts = Map[NonTerminal, NonTerminal]()
      var getDesc = Map[NonTerminal, Set[NonTerminal]]()
      nts foreach { nt =>
        rules(nt) match {
          case AugmentedTerminalsRHS(terminals, VerticalRHS(sons)) =>
            sons.foreach{ son =>
              getAnts += son -> nt
            }
            getDesc += nt -> sons.toSet
          case _ => false
        }
      }
      def getTopmostANT(nt: NonTerminal): NonTerminal = if(getAnts contains(nt)) getTopmostANT(getAnts(nt)) else nt
      def getAncestors(nt: NonTerminal): Set[NonTerminal] = getAnts.get(nt).map(getAncestors).getOrElse(Set.empty[NonTerminal]) + nt
      val startANT = startNonTerminals.map(getTopmostANT).toSet
      def getDescendants(nt: NonTerminal): Set[NonTerminal] = getDesc.get(nt).map((x: Set[NonTerminal]) =>
        x.flatMap((y: NonTerminal) => getDescendants(y) + y)).getOrElse(Set.empty[NonTerminal])
    }
    
    /** Perform horizontal markovization only on the provided non-terminals and their descendants.
     *  @param pred The predicate checking if non-terminals are concerned.
     *  @param recursive If the horizontal context is propagated to ancestors if they are on the RHS of their children.
     */
    def markovize_horizontal_filtered(pred: NonTerminal => Boolean, recursive: Boolean): Grammar = {
      var toDuplicate = Map[NonTerminal, Set[NonTerminal]]()
      var originals = Map[NonTerminal, NonTerminal]()
      def getOriginal(nt: NonTerminal): NonTerminal = {
        originals.get(nt).map(nt2 => if(nt2 != nt) getOriginal(nt2) else nt2).getOrElse(nt)
      }
      val c = new MarkovizationContext(pred) {
        def process_sequence(ls: Seq[Symbol]): List[Symbol] = {
          val (_, res) = ((ListBuffer[Symbol](), ListBuffer[Symbol]()) /: ls) {
            case ((lbold, lbnew), nt: NonTerminal) if pred(nt) =>
              val context_version = nt.copy(hcontext = lbold.toList)
              toDuplicate += nt -> (toDuplicate.getOrElse(nt, Set.empty[NonTerminal]) + context_version)
              if(context_version != nt) originals += context_version -> nt
              for(descendant <- getDescendants(nt) if descendant != nt) {
                val descendant_context_version = descendant.copy(hcontext = lbold.toList)
                toDuplicate += descendant -> (toDuplicate.getOrElse(descendant, Set.empty[NonTerminal]) + descendant_context_version)
                originals += descendant_context_version -> descendant
              }
              for(ascendant <- getAncestors(nt) if ascendant != nt) {
                val acendant_context_version = ascendant.copy(hcontext = lbold.toList)
                toDuplicate += ascendant -> (toDuplicate.getOrElse(ascendant, Set.empty[NonTerminal]) + acendant_context_version)
                originals += acendant_context_version -> ascendant
              }
              (lbold += nt, lbnew += context_version)
            case ((lbold, lbnew), s) =>
              (lbold += s, lbnew += s)
          }
          res.toList
        }
        
        val newStart = process_sequence(start)
        private val newRules = rules.map{ case (k, expansion) =>
          k -> (expansion match {
            case AugmentedTerminalsRHS(terminals, VerticalRHS(children)) =>
              expansion
            case AugmentedTerminalsRHS(terminals, HorizontalRHS(t, children)) =>
              val children_new = process_sequence(t +: children) // Identifies duplicates and differentiates them.
              AugmentedTerminalsRHS(terminals, HorizontalRHS(t, children_new.tail.asInstanceOf[List[NonTerminal]])) 
            case _ => 
              expansion
          })
        }
        
        val newRules2 = for{
            (k, v) <- newRules
            kp <- (toDuplicate.getOrElse(k, Set()) + k)
        } yield {
          v match {
            case AugmentedTerminalsRHS(terminals, VerticalRHS(children)) if toDuplicate.getOrElse(k, Set.empty).nonEmpty =>
              val newChildren = children.map(child => child.copy(hcontext = kp.hcontext))
              kp -> AugmentedTerminalsRHS(terminals, VerticalRHS(newChildren))
            case AugmentedTerminalsRHS(terminals, HorizontalRHS(t, children)) =>
              // Transmit the left context to all ancestors of this node.
              val new_rhs = if(recursive) {
                val ancestors = getAncestors(k)
                val newChildren = children.map(child =>
                  child match { case nt: NonTerminal if ancestors(getOriginal(nt)) => 
                      nt.copy(hcontext = kp.hcontext)
                    case _ => child
                  }
                )
                HorizontalRHS(t, newChildren)
              } else v
              kp -> new_rhs
            case _ =>
               kp -> v
          }
        }
      }
      import c._
      clean(Grammar(newStart, newRules2.toMap))
    }
    
    /** Applies horizontal markovization to the grammar (add the left history to every node and duplicate rules as needed.
      * Is idempotent. */
    def markovize_horizontal(): Grammar = {
      markovize_horizontal_filtered(_ => true, false)
    }
    
    /** Same as vertical markovization, but we add in the vertical context only the nodes coming from a "different abstract hierarchy". Top-level nodes count as a different hierarchy.
      * Different abstract hierarchy means that nodes do not have the same ancestor.
      * @param pred The top-most non-terminals to consider (i.e. abstract ones)
      */
    def markovize_abstract_vertical_filtered(pred: NonTerminal => Boolean): Grammar = {
      val c = new MarkovizationContext(pred) {
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
      }
      import c._
      
      clean(Grammar(start, newRules3))
    }
    
    /** Same as vertical markovization, but we add in the vertical context only the nodes coming from a "different abstract hierarchy"
      * Different abstract hierarchy means that nodes do not have the same ancestor.
      */
    def markovize_abstract_vertical(): Grammar = {
      markovize_abstract_vertical_filtered(_ => true)
    }
    
    /** More general form of markovization, which is similar to introducing states in a top-down tree transducer
     *  We duplicate all m non-terminals n times, and we replace each of them by one of their n variants.
     *  n == 0 yields nothing.
     *  n == 1 yields the original grammar
     *  n == 2 yield all grammars obtained from the original by duplicating each non-terminals and trying all variants.
     **/
    def markovize_all(n: Int): Stream[Grammar] = {
      def variant(nt: NonTerminal, i: Int) = {
        nt.copy(vcontext =  nt.vcontext ++ List.fill(i)(nt))
      }
      val nonTerminalsRHS: Seq[NonTerminal] = {
        (startNonTerminals ++
            (for{(lhs, rhs) <- rules
                  s <-rhs.symbols.collect{ case k: NonTerminal => k } } yield s))
      }
      val nonTerminalsRHSNew: Seq[NonTerminal] = {
        (startNonTerminals ++
            (for{i <- 0 until n // 0 keeps non-terminals the same.
                 (lhs, rhs) <- rules
                  s <-rhs.symbols.collect{ case k: NonTerminal => k } } yield s))
      }
      val nonTerminalsRHSSet = nonTerminalsRHS.toSet
      val variants = nonTerminalsRHSSet.map(nt =>
        nt -> (0 until n).toStream.map(i => variant(nt, i))
      ).toMap
      
      val variantMap = nonTerminalsRHSNew.zipWithIndex.map(nti => nti -> variants(nti._1)).toMap
      val assignments = leon.utils.StreamUtils.cartesianMap(variantMap)
      for(assignment <- assignments) yield {
        var i = 0
        def indexed[T](f: Int => T): T = {
          val res = f(i)
          i += 1
          res
        }
        def copyOfNt(nt: NonTerminal): NonTerminal = indexed { i => assignment((nt, i)) }
        def copy(t: Symbol): Symbol = t match {
          case nt: NonTerminal => copyOfNt(nt)
          case e => e
        }
        val newStart = this.start.map(copy)
        val newRules = for{i <- 0 until n
          (lhs, expansion) <- this.rules
          new_expansion = expansion.map(copy)
        } yield (variant(lhs, i) -> new_expansion)
        Grammar(newStart, newRules.toMap)
      }
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