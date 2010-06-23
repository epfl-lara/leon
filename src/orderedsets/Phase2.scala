package orderedsets

import scala.collection.mutable.{ArrayBuffer, HashMap => MutableMap, HashSet => MutableSet, ListBuffer}
import AST._
import ASTUtil._
import Primitives._
//import z3._

object Flags {
  var useZ3Lib = true
  var intermediateZ3 = true
  var withMinMax = true
  var countOnly = false
  var countNaive = false
  var naiveCounts = List[Int]()
}

object Phase2 {

  //var z3 : Z3Context = null

  def apply(callback: (MyZ3Context, Formula, Order) => Hint)(conj: And) = {
    val (paforms, bapaforms, infs, sups) = ASTUtil.split(conj.formulas)
    val z3 = new MyZ3Context

    //println("PA part"); And(paforms).print
    //println("BAPA part"); And(bapaforms).print

    if (infs.isEmpty && sups.isEmpty) {
      // a non-ordered formula has no orderings
      callback(z3, And(paforms ::: bapaforms), Nil)
    } else {
      //val forms = paforms ::: bapaforms
      val search = new Search(z3, paforms, bapaforms, infs, sups)
      def _callback(order: Order) = callback(z3, And(bapaforms), order)
      guessOrder(z3, _callback)(search.initialNodes, Set() ++ search.symbolToNodeMap.values)
    }
    z3.delete
  }

  private var debug: Search = null

  /**Topological graph **/

  case class UnsatException(msg: String) extends Exception(msg)

  class Node(val _vars: List[IntVar]) {
    // TODO: Are these actually correct !?!! :-S
    var isLEnodes = Set.empty[Node] // Nodes with smaller or equal value
    var isLTnodes = Set.empty[Node] // Nodes with strictly smaller value
    var isGEnodes = Set.empty[Node] // Nodes with greater or equal value
    var isGTnodes = Set.empty[Node] // Nodes with strictly greater value
    var inDegree: Int = -1

    private var myVars = _vars
    private var myelem: Elem = null

    def elem = {
      if (myelem == null) myelem = Elem(this)
      myelem
    }

    def getRepr = myVars.head

    def getVars = myVars

    def addVars(vars: List[IntVar]) {
      myVars :::= vars
      myelem = null
    }

    def initInDegree {
      removeOverlap
      inDegree = isGEnodes.size + isGTnodes.size
      assert((isGEnodes & isGTnodes).isEmpty, "Overlap") // TODO remove
    }

    def varStr = myVars.mkString("{", ",", "}")

    private def addLE(node: Node) {
      this.isLEnodes += node
      node.isGEnodes += this
    }

    private def addGE(node: Node) {
      this.isGEnodes += node
      node.isLEnodes += this
    }

    private def addLT(node: Node) {
      this.isLTnodes += node
      node.isGTnodes += this
    }

    private def addGT(node: Node) {
      this.isGTnodes += node
      node.isLTnodes += this
    }

    private def remLE(node: Node) {
      this.isLEnodes -= node
      node.isGEnodes -= this
    }

    private def remGE(node: Node) {
      this.isGEnodes -= node
      node.isLEnodes -= this
    }

    private def remLT(node: Node) {
      this.isLTnodes -= node
      node.isGTnodes -= this
    }

    private def remGT(node: Node) {
      this.isGTnodes -= node
      node.isLTnodes -= this
    }

    private def addLEs(nodes: Set[Node]) = nodes foreach addLE

    private def addGEs(nodes: Set[Node]) = nodes foreach addGE

    private def addLTs(nodes: Set[Node]) = nodes foreach addLT

    private def addGTs(nodes: Set[Node]) = nodes foreach addGT

    private def remLEs(nodes: Set[Node]) = nodes foreach remLE

    private def remGEs(nodes: Set[Node]) = nodes foreach remGE

    private def remLTs(nodes: Set[Node]) = nodes foreach remLT

    private def remGTs(nodes: Set[Node]) = nodes foreach remGT


    def isEQto(node: Node): List[IntVar] = {
      if (this == node) return Nil
      if (isLTnodes(node) || isGTnodes(node))
        throw UnsatException("Cannot be equal: " + varStr + " = " + node.varStr)

      if (isLEnodes(node) || isGEnodes(node)) {
        var test = false
        test ||= !(this.isGTnodes & node.isLTnodes).isEmpty
        test ||= !(this.isLTnodes & node.isGTnodes).isEmpty
        test ||= !(this.isGTnodes & node.isLEnodes).isEmpty
        test ||= !(this.isLEnodes & node.isGTnodes).isEmpty
        test ||= !(this.isGEnodes & node.isLTnodes).isEmpty
        if (test)
          throw UnsatException("Cannot be equal (sandwich): " + varStr + " = " + node.varStr)

        val circle1 = this.isLEnodes & node.isGEnodes
        val circle2 = this.isGEnodes & node.isLEnodes
        val union = circle1 ++ circle2 + node
        for (n <- union)
          this isEQtoNoRec n

        (union.toList flatMap {_.getVars}).distinct
      } else {
        this isEQtoNoRec node
        node.getVars
      }
    }

    private def isEQtoNoRec(node: Node) {

      this addLEs (node.isLEnodes - this)
      this addLTs node.isLTnodes
      this addGEs (node.isGEnodes - this)
      this addGTs node.isGTnodes

      addVars(node.getVars)

      this remLE node
      this remGE node
      this remLT node
      this remGT node

      // n >= node == this    then rename   node -> this
      for (n <- node.isLEnodes; if n != this) {
        n remGE node
        n addGE this
      }
      // n <= node == this    then rename   node -> this
      for (n <- node.isGEnodes; if n != this) {
        n remLE node
        n addLE this
      }
      // n > node == this    then rename   node -> this
      for (n <- node.isLTnodes) {
        n remGT node
        n addGT this
      }
      // n < node == this    then rename   node -> this
      for (n <- node.isGTnodes) {
        n remLT node
        n addLT this
      }

      this.removeOverlap
      node.removeOverlap

    }


    def isGEto(node: Node): List[IntVar] = {
      if (this == node) return Nil

      if (isLTnodes(node))
        throw UnsatException("Cannot be greater nor equal: " + varStr + " >= " + node.varStr)

      // this >= node && this <= node    implies    this = node 
      // detect circle

      if (isLEnodes(node)) {
        var test = false
        test ||= !(this.isGTnodes & node.isLTnodes).isEmpty
        test ||= !(this.isLTnodes & node.isGTnodes).isEmpty
        test ||= !(this.isGTnodes & node.isLEnodes).isEmpty
        test ||= !(this.isLEnodes & node.isGTnodes).isEmpty
        test ||= !(this.isGEnodes & node.isLTnodes).isEmpty
        if (test)
          throw UnsatException("Cannot be equal (implied sandwich): " + varStr + " = " + node.varStr)

        val circle1 = this.isLEnodes & node.isGEnodes
        val circle2 = this.isGEnodes & node.isLEnodes
        val union = circle1 ++ circle2 + node
        for (n <- union)
          this isEQtoNoRec n

        (union.toList flatMap {_.getVars}).distinct
      } else if (isGTnodes(node) || isGEnodes(node)) {
        Nil
      } else {
        // n > this >= node     implies   n > allStrictSmaller
        for (n <- this.isLTnodes) {
          val allStrictSmaller = node.isGTnodes ++ node.isGEnodes + node
          n addGTs allStrictSmaller
        }
        // this >= node > n    implies   allStrictLarger > n
        for (n <- node.isGTnodes) {
          val allStrictLarger = this.isLTnodes ++ this.isLEnodes + this
          n addLTs allStrictLarger
        }
        // n >= this >= node    implies   n >= node
        for (n <- this.isLEnodes) {
          val allStrictSmaller = node.isGTnodes
          n addGTs allStrictSmaller

          val allNonStrictSmaller = node.isGEnodes + node
          n addGEs allNonStrictSmaller
        }
        // this >= node >= n    implies   this >= n
        for (n <- node.isGEnodes) {
          val allStrictLarger = this.isLTnodes
          n addLTs allStrictLarger

          val allNonStrictLarger = this.isLEnodes + this
          n addLEs allNonStrictLarger
        }
        this addGE node
        this.removeOverlap
        node.removeOverlap
        Nil
      }
    }

    private def removeOverlap {
      this remGEs (isGEnodes & isGTnodes)
      this remLEs (isLEnodes & isLTnodes)
    }

    def isGTto(node: Node) {
      if (this == node || isLTnodes(node) || isLEnodes(node))
        throw UnsatException("Cannot be greater: " + varStr + " > " + node.varStr)

      if (isGTnodes(node)) return

      // n >/>= this > node    implies   n > node
      for (n <- this.isLTnodes ++ this.isLEnodes) {
        val allStrictSmaller = node.isGTnodes ++ node.isGEnodes + node
        n addGTs allStrictSmaller
      }
      // this > node >/>= n    implies   this > n
      for (n <- node.isGTnodes ++ node.isGEnodes) {
        val allStrictLarger = this.isLTnodes ++ this.isLEnodes + this
        n addLTs allStrictLarger
      }

      this addGT node
      this.removeOverlap
      node.removeOverlap
    }

    def decr = {
      inDegree -= 1;
      if (inDegree < 0) {
        checkAllUsed
      }
      (inDegree == 0)
    }

    def incr {inDegree += 1}

    def visit: (List[Node], List[Node]) = {
      val ge = new ListBuffer[Node]
      val gt = new ListBuffer[Node]

      for (node <- this.isLEnodes; if node.decr) ge += node
      for (node <- this.isLTnodes; if node.decr) gt += node
      (ge.toList, gt.toList)
    }

    def unvisit {
      for (node <- isLEnodes) node.incr
      for (node <- isLTnodes) node.incr
    }

    override def toString =
      "NODE " + varStr + "  # " + inDegree +
              isLTnodes.map {_.varStr}.mkString("\n   LT [", ", ", "]") +
              isGTnodes.map {_.varStr}.mkString("\n   GT [", ", ", "]") +
              isLEnodes.map {_.varStr}.mkString("\n   LE [", ", ", "]") +
              isGEnodes.map {_.varStr}.mkString("\n   GE [", ", ", "]")
  }

  /**Search **/

  private class Search(z3: MyZ3Context, _paforms: List[Formula], bapaform: List[Formula], infs: List[(SetVar, IntVar)], sups: List[(SetVar, IntVar)]) {
    val symbolToNodeMap = new MutableMap[IntVar, Node]()
    val infmap = new MutableMap[SetVar, IntVar]()
    val supmap = new MutableMap[SetVar, IntVar]()

    val unorderedInfMap = new MutableMap[SetVar, IntVar]()
    val unorderedSupMap = new MutableMap[SetVar, IntVar]()

    var paforms: List[Formula] = _paforms

    debug = this

    implicit def ivar2node(ivar: IntVar): Node = symbolToNodeMap(ivar)

    def isMapped(ivar1: IntVar, ivar2: IntVar) = (symbolToNodeMap contains ivar1) && (symbolToNodeMap contains ivar2)

    val boundVars = Set.empty ++ infs.map {_._2} ++ sups.map {_._2}
    for (tvar <- boundVars) {
      symbolToNodeMap += tvar -> new Node(List(tvar))
    }
    for (entry@(svar, tvar1) <- infs) infmap get svar match {
      case Some(tvar2) =>
        if (tvar1 != tvar2) {
          paforms = (tvar1 === tvar2) :: paforms
        }
      case None =>
        infmap += entry
    }
    for (entry@(svar, tvar1) <- sups) supmap get svar match {
      case Some(tvar2) =>
        if (tvar1 != tvar2) {
          paforms = (tvar1 === tvar2) :: paforms
        }
      case None =>
        supmap += entry
    }

    val allSets = (Set.empty ++ infmap.keySet ++ supmap.keySet)
    for (svar <- allSets -- supmap.keySet) {
      val sup = Symbol.supOf(svar)
      supmap += svar -> sup
      symbolToNodeMap += sup -> new Node(List(sup))
    }
    for (svar <- allSets -- infmap.keySet) {
      val inf = Symbol.infOf(svar)
      infmap += svar -> inf
      symbolToNodeMap += inf -> new Node(List(inf))
    }

    // Add constraints (TODO equality constraints MUST go first)
    for (f <- paforms) f match {
      case Predicate(EQ, List(TermVar(t1), TermVar(t2))) if isMapped(t1, t2) =>
        for (sym <- t1 isEQto t2)
          symbolToNodeMap(sym) = symbolToNodeMap(t1)
      case _ =>
    }

    for (svar <- allSets) {
      val t1 = infmap(svar)
      val t2 = supmap(svar)
      paforms = (t2 >= t1) :: paforms
    }

    // Exactly as defined in the report
    def infReduce(setExpr: Term): Term = setExpr match {
      case Op(COMPL, _) => Symbol.freshInt
      case Lit(EmptySetLit) => Symbol.freshInt
      case Lit(FullSetLit) => Symbol.freshInt

      case Op(UNION, trmLst) => Op(MIN, trmLst map infReduce)
      case Op(INTER, trmLst) => Op(MAX, trmLst map infReduce)
      case TermVar(v) if infmap.contains(v) => infmap(v)
      case TermVar(v) if unorderedInfMap.contains(v) => unorderedInfMap(v)
      case TermVar(v) => {val tf = Symbol.freshInt; unorderedInfMap(v) = tf; tf}
      case _ => error("infReduce: Got:" + setExpr + "\n Set Expression expected")
    }

    def supReduce(setExpr: Term): Term = setExpr match {
      case Op(COMPL, _) => Symbol.freshInt
      case Lit(EmptySetLit) => Symbol.freshInt
      case Lit(FullSetLit) => Symbol.freshInt

      case Op(UNION, trmLst) => Op(MAX, trmLst map supReduce)
      case Op(INTER, trmLst) => Op(MIN, trmLst map supReduce)
      case TermVar(v) if supmap.contains(v) => supmap(v)
      case TermVar(v) if unorderedSupMap.contains(v) => unorderedSupMap(v)
      case TermVar(v) => {val tf = Symbol.freshInt; unorderedSupMap(v) = tf; tf}
      case _ => error("supReduce: Got:" + setExpr + "\n Set Expression expected")
    }

    // TODO: Does not handle the card(A) > 0 like constrants
    // TODO: How to handle seq to {} ?
    if (Flags.withMinMax)
      for (f <- bapaform) f match {
        case Predicate(SEQ, List(s1, s2)) => {
          val lhsInf = infReduce(s1)
          val rhsInf = infReduce(s2)
          // TODO: Complemented set variables should be handled elegantly
          val setVars = setvars(f)
          if (setVars.forall(infmap.contains(_))) z3.impose(lhsInf === rhsInf)

          addConstraint(lhsInf === rhsInf)

          val lhsSup = supReduce(s1)
          val rhsSup = supReduce(s2)
          if (setVars.forall(supmap.contains(_))) z3.impose(lhsSup === rhsSup)

          addConstraint(lhsSup === rhsSup)
        }
        case Predicate(SUBSETEQ, List(s1, s2)) => {
          val lhsInf = infReduce(s1)
          val rhsInf = infReduce(s2)
          addConstraint(lhsInf >= rhsInf)

          val lhsSup = supReduce(s1)
          val rhsSup = supReduce(s2)
          addConstraint(rhsSup >= lhsSup)
        }
        case _ =>
      }

    // TODO: Magic/dirty work
    // This received formula of the form:
    // { MIN( .... ) or MAX( ... ) or IntVar } { <= or === } { MIN( .... ) or MAX( ... ) or IntVar }
    def addConstraint(form: Formula) = {

      //println("Got formula = " + form)

      val tempSymbolToNodeMap = new MutableMap[IntVar, Node]()
      for (v <- intvars(form)) {
        tempSymbolToNodeMap(v) = new Node(List(v))
      }

      def makeMinMaxGraph(setExpr: Term): Node = setExpr match {
        case Op(MIN, trmLst) => {
          val tf = Symbol.freshInt;
          tempSymbolToNodeMap(tf) = new Node(List(tf))
          val nodesGreaterThanThis = trmLst map makeMinMaxGraph
          for (n <- nodesGreaterThanThis) {
            for (sym <- n isGEto tempSymbolToNodeMap(tf)) {
              tempSymbolToNodeMap(sym) = n
            }
          }
          tempSymbolToNodeMap(tf)
        }
        case Op(MAX, trmLst) => {
          val tf = Symbol.freshInt
          tempSymbolToNodeMap(tf) = new Node(List(tf))
          val nodesLessThanThis = trmLst map makeMinMaxGraph
          for (n <- nodesLessThanThis) {
            for (sym <- tempSymbolToNodeMap(tf) isGEto n) {
              tempSymbolToNodeMap(sym) = tempSymbolToNodeMap(tf)
            }
          }
          tempSymbolToNodeMap(tf)
        }
        case TermVar(v) => tempSymbolToNodeMap(v)
        case _ => error("makeMinMaxGraph: Got = " + setExpr + "\nExpecting SetExpression.")
      }

      form match {
        case Predicate(EQ, t1 :: t2 :: Nil) => {
          val lhsNode = makeMinMaxGraph(t1)
          val rhsNode = makeMinMaxGraph(t2)
          for (sym <- lhsNode isEQto rhsNode) {
            tempSymbolToNodeMap(sym) = lhsNode
          }
        }
        case Predicate(GE, t1 :: t2 :: Nil) => {
          val lhsNode = makeMinMaxGraph(t1)
          val rhsNode = makeMinMaxGraph(t2)
          for (sym <- lhsNode isGEto rhsNode) {
            tempSymbolToNodeMap(sym) = lhsNode
          }
        }
        case _ => error("addConstraint: Got = " + form + "\nExpecting EQ or GE.")
      }

      for ((v, n) <- tempSymbolToNodeMap) {
        if (symbolToNodeMap.contains(v)) {
          for (k <- n.getVars; if k != v) {
            if (symbolToNodeMap.contains(k)) {
              //println("Adding: " + v + " = " + k)
              paforms = (v === k) :: paforms
            }
          }
          for (nodeGEtoV <- n.isLEnodes) {
            for (k <- nodeGEtoV.getVars) {
              if (symbolToNodeMap.contains(k)) {
                //println("Adding: " + v + " <= " + k)
                paforms = (v <= k) :: paforms
              }
            }
          }
          for (nodeGTtoV <- n.isLTnodes) {
            for (k <- nodeGTtoV.getVars) {
              if (symbolToNodeMap.contains(k)) {
                //println("Adding: " + v + " < " + k)
                paforms = (v < k) :: paforms
              }
            }
          }
          // The rest of cases not checked because of Transitive closure
        }
      }
    }

    for (f <- paforms) f match {
    // TODO remove matched predicates from formula ?
      case Predicate(LT, List(TermVar(t1), TermVar(t2))) if isMapped(t1, t2) => t2 isGTto t1
      case Predicate(GT, List(TermVar(t1), TermVar(t2))) if isMapped(t1, t2) => t1 isGTto t2
      case Predicate(LE, List(TermVar(t1), TermVar(t2))) if isMapped(t1, t2) =>
        for (sym <- t2 isGEto t1)
          symbolToNodeMap(sym) = symbolToNodeMap(t2)
      case Predicate(GE, List(TermVar(t1), TermVar(t2))) if isMapped(t1, t2) =>
        for (sym <- t1 isGEto t2)
          symbolToNodeMap(sym) = symbolToNodeMap(t1)
      case Predicate(EQ, List(TermVar(t1), TermVar(t2))) if isMapped(t1, t2) =>
        for (sym <- t1 isEQto t2)
          symbolToNodeMap(sym) = symbolToNodeMap(t1)
      case _ =>
    }

    val nodes = symbolToNodeMap.values.toList.distinct
    for (n <- nodes) n.initInDegree
    val initialNodes = (for (n <- nodes; if n.inDegree == 0) yield n) sortWith (_.getVars.head.name < _.getVars.head.name)

    // Create inf/sup to set data structure
    for (termvar <- symbolToNodeMap.keys) {
      termvar.infOfList = Set.empty[Symbol] ++ (for ((set, x) <- infmap; if termvar == x) yield set)
      termvar.supOfList = Set.empty[Symbol] ++ (for ((set, x) <- supmap; if termvar == x) yield set)
    }

    if (Flags.countNaive) {
      Flags.naiveCounts = initialNodes.size :: Flags.naiveCounts
      throw new UnsatException("(Just counting)")
    }

    z3.impose(And(paforms))
    if (!z3.isStillSAT) {
      //println("Z3 detected the PA-formula to be UNSAT.")
      throw (new UnsatException("Z3 found this to be UNSAT."))
    }
  }

  /**Guess Ordering */

  private def pickOne[A](list: List[A]): List[(List[A], A, List[A])] = {
    val front = new ListBuffer[A]
    var back = list
    val buffer = new ListBuffer[(List[A], A, List[A])]
    while (back != Nil) {
      val elem = back.head
      back = back.tail
      buffer += ((front toList, elem, back))
      front += elem
    }
    buffer.toList
  }

  private def sortWithInfPriority(list: List[Node]) = {
    val front = new ListBuffer[Node]
    val back = new ListBuffer[Node]
    var _list = list
    while (_list != Nil) {
      _list.head.elem match {
        case _: InfElem => front += _list.head
        case _ => back += _list.head
      }
      _list = _list.tail
    }
    front ++= back
    front.toList
  }

  private def sortWithSupPriority(list: List[Node]) = {
    val front = new ListBuffer[Node]
    val back = new ListBuffer[Node]
    var _list = list
    while (_list != Nil) {
      _list.head.elem match {
        case _: SupElem => front += _list.head
        case _ => back += _list.head
      }
      _list = _list.tail
    }
    front ++= back
    front.toList
  }

  private def pickOneWithInfPriority(list: List[Node]) = pickOne(sortWithInfPriority(list))

  private def pickOneWithSupPriority(list: List[Node]) = pickOne(sortWithSupPriority(list))



  object Elem {
    def apply(node: Node) = (filterInfs(node.getVars), filterSups(node.getVars)) match {
    // TODO this is a hack
      case (Nil, Nil) =>
        println(node)
        error("fail") // InfElem(node.getVars)
      case (infs, Nil) => InfElem(infs)
      case (Nil, sups) => SupElem(sups)
      case (infs, sups) => ComboElem(infs, sups, false)
    }
  }
  sealed trait Elem {
    def isSup = false

    def ++(node: Node): Option[Elem] = ++(Elem(node))

    def ++(elem: Elem): Option[Elem] = (this, elem) match {
      case (InfElem(a), InfElem(b)) => Some(InfElem(a ::: b))
      case (SupElem(x), SupElem(y)) => Some(SupElem(x ::: y))

      case (InfElem(a), SupElem(y)) => None // Some(ComboElem(a, y, false)) //None // Magic


      case (SupElem(x), InfElem(b)) => Some(ComboElem(b, x, false))
      case (InfElem(a), ComboElem(b, y, _)) => Some(ComboElem(a ::: b, y, false))
      case (SupElem(x), ComboElem(b, y, _)) => Some(ComboElem(b, x ::: y, false))
      case (ComboElem(a, x, _), InfElem(b)) => Some(ComboElem(a ::: b, x, false))
      case (ComboElem(a, x, _), SupElem(y)) => Some(ComboElem(a, x ::: y, false))
      case (ComboElem(a, x, _), ComboElem(b, y, _)) => Some(ComboElem(a ::: b, x ::: y, false))
    }

    def vars = this match {
      case InfElem(infs) => infs
      case SupElem(sups) => sups
      case ComboElem(infs, sups, _) => infs ::: sups
    }

    override def toString = this match {
      case InfElem(infs) => infs.mkString("I{", ",", "}")
      case SupElem(sups) => sups.mkString("S{", ",", "}")
      case ComboElem(infs, sups, true) =>
        infs.mkString("I{", ",", "}") + " <= " + sups.mkString("S{", ",", "}")
      case ComboElem(infs, sups, false) =>
        infs.mkString("I{", ",", "}") + " = " + sups.mkString("S{", ",", "}")
    }

    def normalize = this match {
      case ComboElem(infs, Nil, _) => InfElem(infs)
      case ComboElem(Nil, sups, _) => SupElem(sups)
      case _ => this
    }

    def getRepr = vars.head
  }
  case class InfElem(infs: List[IntVar]) extends Elem
  case class SupElem(sups: List[IntVar]) extends Elem {
    override def isSup = true
  }
  case class ComboElem(infs: List[IntVar], sups: List[IntVar], isLe: Boolean) extends Elem


  private type Queue = List[Node]
  private type RecOrder = List[Elem]
  //type Order = List[List[IntVar]]
  type Order = List[Elem]
  type Hint = Boolean

  def merge(z3: MyZ3Context, order: Order): Order = order match {
    case InfElem(a) :: SupElem(x) :: rest =>
      ComboElem(a, x, true) :: merge(z3, rest)
    case first :: second :: rest =>
      z3.impose(first.getRepr < second.getRepr)
      first :: merge(z3, second :: rest)
    case List(first) => first :: Nil
    case Nil => Nil
  }

  private def guessOrder(z3: MyZ3Context, callback: Order => Hint): (Queue, Set[Node]) => Unit = {

    def rek(current: Queue, later: Queue, acc: RecOrder, toBeGuessed: Set[Node]) {
      if (Flags.intermediateZ3) {
        if (!z3.isStillSAT) {
          println("HURRAY at " + toBeGuessed.size)
          return
        }
      }

      if (current.isEmpty && later.isEmpty) {
        //checkAllUsed
        val order = merge(z3, acc.reverse map {_.normalize})

        if (Flags.intermediateZ3) {
          if (!z3.isStillSAT) {
            println("HURRAY at " + toBeGuessed.size)
            return
          }
        }

        val hint = callback(order)
        ()
      } else {
        // guess same equivalence class
        val pickList = if (acc.head.isSup) pickOneWithSupPriority(current) else pickOneWithInfPriority(current)
        for ((front, node, back) <- pickList) {
          acc.head ++ node match {
            case Some(elem) =>
              val (ge, gt) = node.visit
              val restNodes = toBeGuessed - node
              z3.push
              z3.impose(acc.head.getRepr === node.getRepr)
              for (ii <- restNodes)
                z3.impose(node.getRepr <= ii.getRepr)
              rek(back ::: ge, front ::: later ::: gt, elem :: acc.tail, restNodes)
              z3.pop
              node.unvisit
            case None =>
          }
        }
        // guess next equivalence class
        for ((front, node, back) <- pickOneWithInfPriority(current ::: later)) {
          val (ge, gt) = node.visit
          val restNodes = toBeGuessed - node
          z3.push
          z3.impose(acc.head.getRepr < node.getRepr)
          for (ii <- restNodes)
            z3.impose(node.getRepr <= ii.getRepr)
          rek(back ::: ge, front ::: gt, Elem(node) :: acc, restNodes)
          z3.pop
          node.unvisit
        }
      }
    }
    // guess first equivalence class
    (list: Queue, toBeGuessed: Set[Node]) => {

      //for (node <- toBeGuessed) println(node)


      for ((front, node, back) <- pickOneWithInfPriority(list)) {
        val (ge, gt) = node.visit
        val restNodes = toBeGuessed - node
        z3.push
        for (ii <- restNodes)
          z3.impose(node.getRepr <= ii.getRepr)

        rek(back ::: ge, front ::: gt, List(Elem(node)), restNodes)

        z3.pop
        node.unvisit
      }
    }
  }


  def order2string(order: Order) = order mkString "  <  "

  object OrderingCounter extends ((Formula, Order, Boolean) => Hint) {
    def apply(form: Formula, order: Order, x: Boolean): Hint = {
      Phase3.orderCount += 1
      println("Order " + Phase3.orderCount + "      " + Phase2.order2string(order))
      true
    }
  }

  /*
  def debugCheckGraph = {
    val nodes = debug.symbolToNodeMap.values.toList
    for (node <- nodes) {
      for (n <- node.isLEnodes; if !(n.isGEnodes contains node)) {
        println("Found problem:")
        println("  " + node.varStr + " <= " + n.varStr)
        println("  but not vice-versa")
        error("stop")
      }
      for (n <- node.isGEnodes; if !(n.isLEnodes contains node)) {
        println("Found problem:")
        println("  " + node.varStr + " >= " + n.varStr)
        println("  but not vice-versa")
        error("stop")
      }
      for (n <- node.isLTnodes; if !(n.isGTnodes contains node)) {
        println("Found problem:")
        println("  " + node.varStr + " < " + n.varStr)
        println("  but not vice-versa")
        error("stop")
      }
      for (n <- node.isGTnodes; if !(n.isLTnodes contains node)) {
        println("Found problem:")
        println("  " + node.varStr + " > " + n.varStr)
        println("  but not vice-versa")
        error("stop")
      }
      
      
    }
  }*/

  def checkAllUsed = {
    val nodes = debug.symbolToNodeMap.values.toList
    val bad = for (node <- nodes; if node.inDegree > 0) yield node

    if (!bad.isEmpty) {
      //debugCheckGraph
      println
      println("Alllll: " + nodes.mkString("\n  ", ", \n  ", ""))
      println
      println("Baaaad: " + bad.mkString("\n  ", ", \n  ", ""))
      println
      System.out.flush
      error("Some nodes were not added to the ordering !")
    }
  }
}
