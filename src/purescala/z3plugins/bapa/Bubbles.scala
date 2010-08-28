package purescala.z3plugins.bapa

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap, ArrayBuffer}
// , BitSet => MutableBitSet}
// import scala.collection.immutable.{BitSet => IDSet}
import scala.collection.{BitSet}
import z3.scala._
import AST._
import NormalForms.simplify

trait Bubbles {
  //val SHOW_STATISTICS = false
  val SHOW_STATISTICS = true


  val z3: Z3Context
  private[bapa] val mkDomainSize: Z3AST

  protected def assertAxiomSafe(ast: Z3AST): Unit

  protected def treeToZ3(tree: Tree): Z3AST

  protected def BubbleBapaToPaTranslator(tree: Tree): Tree

  private def assertAxiomSafe(tree: Tree) {
    assertAxiomSafe(treeToZ3(simplify(tree)))
  }

  type IDSet = BitSet
  type VRSet = BitSet
  type IDList = Seq[Int]

  case class SetName(name: String, sym: Symbol) {
    def complName = name.toLowerCase

    override def toString = name
  }

  case class VennRegion(name: String, ast: Z3AST) {
    def toTree = Var(IntSymbol(ast))

    override def toString = name
  }

  /* Cache */

  private val cachedSymbolIDs = MutableMap[Symbol, Int]()
  private val cachedSymbols = new ArrayBuffer[Symbol]()
  private val cachedRegions = MutableMap[String, VennRegion]()
  //   private var idCounter = -1
  private val mkZero = z3.mkInt(0, z3.mkIntSort)

  private def mkID(symbol: Symbol) = {
    cachedSymbolIDs getOrElse (symbol, {
      val id = cachedSymbols.size
      cachedSymbols += symbol
      cachedSymbolIDs(symbol) = id
      //       println ("mkName  " + symbol + " -> " + mkName(id))
      id
    })
  }

  private def mkName(id: Int) = ('A' + id).toChar.toString

  private def mkSym(id: Int) = cachedSymbols(id)

  private def mkRegion(idList: IDList, bitset: Long) = {
    //     val region: IDSet = ...
    def region(i: Int) = ((1L << i) & bitset) != 0
    val names = for (i <- 0 until idList.size) yield
      if (region(i)) mkName(idList(i))
      else mkName(idList(i)).toLowerCase
    val name = names.mkString
    cachedRegions getOrElse (name, {
      val region = VennRegion(name, z3.mkFreshConst(name, z3.mkIntSort))
      cachedRegions(name) = region
      region
    })
  }

  /* Bubbles ! */

  sealed abstract class AbstractBubble(val label: IDSet) {
    val ids: IDList = label.toSeq sortWith {_ < _}
    lazy val vennRegions: Array[VennRegion] = (Array tabulate (1 << ids.size)) {i => mkRegion(ids, i)}

    def numSetVars = ids.size

    def mkVennAxiom = {
      z3.mkAnd(
        // Non-negative
        z3.mkAnd((vennRegions map {
          region =>
            z3.mkGE(region.ast, mkZero)
        }): _*
          ),
        // Sum is domain size
        z3.mkEq(
          mkDomainSize,
          z3.mkAdd((vennRegions map {_.ast}): _*)
          )
        )
    }

    def translate(tree: Tree): Tree = {
      val regions = translate0(tree).toSeq.sortWith {_ < _} map {i => vennRegions(i).toTree}
      if (regions.size > 0) Op(ADD, regions) else 0
      //       val regions = translate0(tree).toSeq.sortWith{_ < _} map {i => vennRegions(i).ast}
      //       if (regions.size > 0) z3.mkAdd(regions:_*) else mkZero
    }

    private def translate0(tree: Tree): VRSet = tree match {
      case Lit(EmptySetLit) =>
        BitSet.empty
      case Op(COMPL, Seq(Lit(EmptySetLit))) =>
        BitSet((0 until vennRegions.size): _*)
      case Var(sym) =>
        if (sym.typ != SetType) error("Not a set variable : " + sym)
        val setNum = ids indexOf mkID(sym)
        if (setNum == -1) error("Unknown set '" + sym + "' aka " + mkName(mkID(sym)) + " in this bubble/edge : " + this)
        val regions = for (i <- 0 until vennRegions.size; if (i & (1 << setNum)) != 0) yield i
        BitSet(regions: _*)
      case Op(COMPL, Seq(Var(sym))) =>
        if (sym.typ != SetType) error("Not a set variable : " + sym)
        val setNum = ids indexOf mkID(sym)
        if (setNum == -1) error("Unknown set '" + sym + "' aka " + mkName(mkID(sym)) + " in this bubble/edge : " + this)
        val regions = for (i <- 0 until vennRegions.size; if (i & (1 << setNum)) == 0) yield i
        BitSet(regions: _*)
      case Op(UNION, ts) =>
        ts map translate0 reduceLeft {_ ++ _}
      case Op(INTER, ts) =>
        ts map translate0 reduceLeft {_ & _}
      case _ =>
        error("Not a simplified set expression : " + tree)
    }
  }

  // Node in Hyper-tree
  class Bubble(label: IDSet) extends AbstractBubble(label) {
    val edges = MutableSet[HyperEdge]()
    var refCount = 0
    var component: Bubble = null

    def setVars = label map mkSym

    def numIntVars = vennRegions.size

    def toLongString = toString + "  ref = " + refCount + "  comp = " + component + "  edges = " + edges

    override def toString = "b" + (label map mkName).mkString("(", "", ")")

    override def hashCode = label.hashCode

    override def equals(that: Any) =
      (that != null &&
              that.isInstanceOf[Bubble] &&
              that.asInstanceOf[Bubble].label == this.label)

    def mkImpliedEqAxioms = {
      val buffer = new ArrayBuffer[Z3AST]()
      val B = (Array tabulate ids.size)(i => mkSym(ids(i)))
      for (i <- 0 until B.size; j <- 0 until i) {
        val bapaTree = B(i) seteq B(j)
        val paTree = BubbleBapaToPaTranslator(bapaTree)
        buffer += z3.mkImplies(
          treeToZ3(paTree),
          treeToZ3(bapaTree)
          )
      }
      buffer
    }
  }

  // Edge in Hyper-tree
  class HyperEdge(label: IDSet) extends AbstractBubble(label) {
    val nodes = MutableSet[Bubble]()

    def addNode(bubble: Bubble) {
      bubble.edges += this
      nodes += bubble
    }

    def numIntVars = {
      if (nodes exists {label subsetOf _.label}) {
        0
      } else {
        vennRegions.size
      }
    }

    def toLongString = toString + "  nodes = " + nodes

    override def toString = "e" + (label map mkName).mkString("(", "", ")")

    override def hashCode = label.hashCode

    override def equals(that: Any) =
      (that != null &&
              that.isInstanceOf[HyperEdge] &&
              that.asInstanceOf[HyperEdge].label == this.label)

    def mkAgreeAxioms = {
      val buffer = new ArrayBuffer[Tree]()
      for (node <- nodes) {
        val axiom = mkAxiom(node)
        if (axiom != null)
          buffer += axiom
      }
      buffer
    }

    private def mkAxiom(bubble: Bubble) = {
      val common = bubble.label & this.label
      val buffer = new ArrayBuffer[Tree]()
      def rec(ids: List[Int], sets: List[Tree]): Unit = ids match {
        case Nil =>
          val tree = Op(INTER, sets)
          buffer += (bubble translate tree) === (this translate tree)
        case s :: ss =>
          rec(ss, ~mkSym(s) :: sets)
          rec(ss, mkSym(s) :: sets)
      }
      if (bubble.label != this.label) {
        rec((bubble.label & this.label).toList, Nil)
        Op(AND, buffer)
      } else {
        null
      }
    }
  }

  private def unionFind(a: Bubble, b: Bubble, union: Boolean) = {
    var _a = a
    var _b = b
    var x = a
    var y = b
    while (x.component ne null) x = x.component
    while (y.component ne null) y = y.component
    while (_a.component ne null) {
      val t = _a
      _a = _a.component
      t.component = x
    }
    while (_b.component ne null) {
      val t = _b
      _b = _b.component
      t.component = y
    }
    if (union && (x ne y)) {
      y.component = x
    }
    (x eq y)
  }

  def idToName(ids: IDSet) = ids map mkName
  // 

  // Universe (home of the bubbles)
  object Universe {
    val allBubbles = MutableMap[IDSet, Bubble]()
    val allEdges = MutableMap[IDSet, HyperEdge]()

    def addBubble(symbols: Set[Symbol]) = {
      val symIDs = BitSet((symbols.toSeq map mkID): _*)

      allBubbles find {symIDs subsetOf _._1} match {
        case Some((_, bubble)) =>
          bubble.refCount += 1
          bubble
        case None =>
          // Create new bubble
          val bubble = new Bubble(symIDs)

          // Find common sets
          val intersections = for (bIDs <- allBubbles.keySet) yield bIDs & symIDs
          var core = Set[IDSet]()
          for (set <- intersections; if !set.isEmpty) {
            core = core filterNot {_ subsetOf set}
            if (!(core exists {set subsetOf _})) {
              core = core + set
            }
          }
          allBubbles(symIDs) = bubble

          // Create connections
          for (set <- core) {
            val bubbles = for (b <- allBubbles.values; if (b.label & set).nonEmpty) yield b
            val edge = collapseCycles(bubbles.toSeq, set)
            allEdges(edge.label) = edge
          }

          // Assert Axioms
          assertAxiomSafe(bubble.mkVennAxiom)
          bubble.mkImpliedEqAxioms foreach assertAxiomSafe
          for (edge <- bubble.edges) {
            assertAxiomSafe(edge.mkVennAxiom)
            edge.mkAgreeAxioms foreach assertAxiomSafe
          }

          if (SHOW_STATISTICS) showStatistics

          bubble.refCount += 1
          bubble
      }
    }

    private def collapseCycles(initialNodes: Seq[Bubble], initialLabel: IDSet) = {
      val nodesInNewEdge = MutableSet[Bubble](initialNodes: _*)
      var labelOfNewEdge = initialLabel
      // Merge and remove an edge 
      def mergeEdge(edge: HyperEdge) {
        nodesInNewEdge ++= edge.nodes
        labelOfNewEdge ++= edge.label
        edge.nodes foreach {_.edges -= edge}
        edge.nodes.clear
        allEdges -= edge.label
      }
      // Find the paths from one bubble to some others
      def dfs(from: Bubble, to: Set[Bubble]) {
        val seen = MutableSet[Bubble](from)
        val prev = MutableMap[Bubble, (Bubble, HyperEdge)]()
        var stack = List(from)
        var numFound = 0
        while (stack.nonEmpty && numFound < to.size) {
          val node = stack.head
          stack = stack.tail
          for (edge <- node.edges; next <- edge.nodes; if !seen(next)) {
            seen(next) = true
            stack = next :: stack
            prev(next) = (node, edge)
          }
          if (to(node)) {
            numFound += 1
            var n = node
            while (n ne from) {
              val (b, e) = prev(n)
              if (e != null) {
                mergeEdge(e)
                prev(n) = (b, null)
              }
              n = b
            }
          }
        }
        if (numFound != to.size) error("Could not find all destinations !!!")
      }
      // Partition into components and collapse inner paths
      val partitions = MutableMap[Bubble, MutableSet[Bubble]]()
      for (node <- initialNodes) partitions find {n => unionFind(node, n._1, false)} match {
        case Some((_, set)) => set += node
        case None => partitions(node) = MutableSet[Bubble]()
      }
      for ((from, to) <- partitions; if to.nonEmpty) dfs(from, to.toSet)
      val first = partitions.keys.iterator.next
      for (node <- partitions.keys) unionFind(first, node, true)
      // Build edge
      val edge = new HyperEdge(labelOfNewEdge)
      nodesInNewEdge foreach edge.addNode
      edge
    }
    /*
    def removeBubble(symbols: Set[Symbol]) {
      val label = BitSet((symbols.toSeq map mkID):_*)
      allBubbles find {label subsetOf _._1} match {
        case Some((_, bubble)) =>
          bubble.refCount -= 1
          if (bubble.refCount == 0) {
            // TODO ...
          }
        case None =>
          error("should not happen")
      }
      error("unimplemented")
    }
    */

    /*
    def showState {
      println("------------")
      println("Bubbles :")
      allBubbles.values foreach {x => println(x toLongString)}
      println
      
      println("Edges :")
      allEdges.values foreach {x => println(x toLongString)}
      println
    }
    */

  }

  /* Misc */

  def showStatistics {

    val setVars = MutableSet[Symbol]()
    val bubbleSizes = new ArrayBuffer[Int]()
    val edgeSizes = new ArrayBuffer[Int]()
    var bubbleSum = 0
    var edgeSum = 0

    for (bubble <- Universe.allBubbles.values) {
      bubbleSizes += bubble.numSetVars
      bubbleSum += bubble.numIntVars
      setVars ++= bubble.setVars
    }
    for (edge <- Universe.allEdges.values) {
      edgeSizes += edge.numSetVars
      edgeSum += edge.numIntVars
    }

    println("________________________________________")
    println
    println("# set variables            : " + setVars.size)
    println("# bubbles                  : " + bubbleSizes.size)
    println("# venn regions for bubbles : " + bubbleSum)
    println("# hyper edges              : " + edgeSizes.size)
    println("# venn regions for edges   : " + edgeSum)
    println("# venn regions (total)     : " + (bubbleSum + edgeSum))
    println("________________________________________")
    println
    println("Bubble sizes  : " + bubbleSizes.mkString("{", ", ", "}"))
    println("Edge sizes    : " + bubbleSizes.mkString("{", ", ", "}"))
    println("Set variables : " + setVars.mkString("{", ", ", "}"))
    println
  }

}
