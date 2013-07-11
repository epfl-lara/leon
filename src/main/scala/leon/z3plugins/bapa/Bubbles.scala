/* Copyright 2009-2013 EPFL, Lausanne */

package purescala.z3plugins.bapa

import scala.collection.mutable.{HashSet => MutableSet, HashMap => MutableMap, ArrayBuffer}
import scala.collection.{BitSet}
import z3.scala._
import AST._
import NormalForms.simplify

import scala.sys.error

trait Bubbles {

  /* Flags */
  
//   val SHOW_INTERMEDIATE_STATISTICS = true
  val SHOW_INTERMEDIATE_STATISTICS = false

//   val SHOW_STATISTICS = true
  val SHOW_STATISTICS = false


  /* Connection to theory plugin */

  val z3: Z3Context
  
  private[bapa] val mkDomainSize: Z3AST

  protected def assertAxiomSafe(ast: Z3AST): Unit

  protected def treeToZ3(tree: Tree): Z3AST
    
  protected def z3ToTree(ast: Z3AST): Tree

  protected def BubbleBapaToPaTranslator(tree: Tree): Tree

  private def assertAxiomSafe(tree: Tree) {
    assertAxiomSafe(treeToZ3(simplify(tree)))
  }

  /* Definitions */

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

  /* Cache of venn regions */

  private val cachedSymbolIDs = MutableMap[Symbol, Int]()
  private val cachedSymbols = new ArrayBuffer[Symbol]()
  private val cachedRegions = MutableMap[String, VennRegion]()
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

  def idToName(ids: IDSet) = ids map mkName

  
  /* Bubbles */

  sealed abstract class AbstractBubble(val label: IDSet) {
    val ids: IDList = label.toSeq sortWith {_ < _}
    lazy val vennRegions: Array[VennRegion] = (Array tabulate (1 << ids.size)) {i => mkRegion(ids, i)}
    
    def numSetVars = ids.size
    
    def numFreeIntVars: Int
    
    def numVennRegions = vennRegions.size
    
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
        (ts map translate0 foldLeft BitSet.empty){_ ++ _}
      case Op(INTER, ts) =>
        val fullSet = BitSet((0 until vennRegions.size): _*)
        (ts map translate0 foldLeft fullSet){_ & _}
      case _ =>
        error("Not a simplified set expression : " + tree)
    }
  }

  // Node in Hyper-tree
  class Bubble(label: IDSet) extends AbstractBubble(label) {
    val edges = MutableSet[HyperEdge]()
    var component: Bubble = null
    
    def setVars = label map mkSym
    
    def numFreeIntVars = ids.size
    
    def toLongString = toString + "  comp = " + component + "  edges = " + edges
    
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
    
    def numFreeIntVars = {
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

  /* Universe */
  
  object Universe {
    val allBubbles = MutableMap[IDSet, Bubble]()
    val allEdges = MutableMap[IDSet, HyperEdge]()
    
    def addBubble(symbols: Set[Symbol]): (Bubble, Boolean) = {
      val symIDs = BitSet((symbols.toSeq map mkID): _*)
      
      allBubbles find {symIDs subsetOf _._1} match {
        case Some((_, bubble)) =>
          (bubble, false)
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
          
          if (SHOW_INTERMEDIATE_STATISTICS) showInfo2
          
          (bubble, true)
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
//       val oneNode = initialNodes.iterator.next
//       partitions(oneNode) = initialNodes.toSet - oneNode
      for (node <- initialNodes) partitions find {n => unionFind(node, n._1, false)} match {
        case Some((_, set)) => set += node
        case None => partitions(node) = new MutableSet[Bubble]()
      }
      for ((from, to) <- partitions; if to.nonEmpty) dfs(from, to.toSet)
      val first = partitions.keys.iterator.next
      for (node <- partitions.keys) unionFind(first, node, true)
      // Build edge
      val edge = new HyperEdge(labelOfNewEdge)
      nodesInNewEdge foreach edge.addNode
      edge
    }
    
    def removeBubble(node: Bubble) {
      def rebuildUnionFind {
        for (bubble <- allBubbles.values) bubble.component = null
        for (edge <- allEdges.values) {
          val node1 = edge.nodes.iterator.next
          for (node <- edge.nodes; if node != node1)
            unionFind(node1, node, true)
        }
      }
      for (edge <- node.edges) {
        edge.nodes -= node
        if (edge.nodes.size <= 1) {
          edge.nodes foreach {_.edges -= edge}
          edge.nodes.clear
          allEdges -= edge.label
        } else {
          var labelOfNewEdge = BitSet.empty
          for (node1 <- edge.nodes; node2 <- edge.nodes; if node1 != node2) {
            labelOfNewEdge ++= node1.label & node2.label
          }
          if (!(labelOfNewEdge subsetOf edge.label)) {
            println("edge : " + edge.label)
            println("new  : " + labelOfNewEdge)
          }
          require(labelOfNewEdge subsetOf edge.label)
          if (labelOfNewEdge.size < edge.label.size) {
            val nodesInNewEdge = new ArrayBuffer() ++ edge.nodes
            edge.nodes foreach {_.edges -= edge}
            edge.nodes.clear
            allEdges -= edge.label
            // Build edge
            val newEdge = new HyperEdge(labelOfNewEdge)
            nodesInNewEdge foreach newEdge.addNode
            allEdges(newEdge.label) = newEdge
            assertAxiomSafe(newEdge.mkVennAxiom)
            newEdge.mkAgreeAxioms foreach assertAxiomSafe
          }
        }
      }
      node.edges.clear
      allBubbles -= node.label
      rebuildUnionFind
    }
    
//     /*
    def showState {
      println("------------")
      println("Bubbles :")
      allBubbles.values foreach {x => println(x.toLongString)}
      println
      
      println("Edges :")
      allEdges.values foreach {x => println(x.toLongString)}
      println
    }
//     */
  }

  /* Misc */

  def showInfo = if (SHOW_STATISTICS) showInfo2

  def showInfo2 {
    
    val setVars = MutableSet[Symbol]()
    val bubbleSizes = new ArrayBuffer[Int]()
    val edgeSizes = new ArrayBuffer[Int]()
    var bubbleSum = 0
    var edgeSum = 0
    
    for (bubble <- Universe.allBubbles.values) {
      bubbleSizes += bubble.numSetVars
      bubbleSum += bubble.numFreeIntVars
      setVars ++= bubble.setVars
    }
    for (edge <- Universe.allEdges.values) {
      edgeSizes += edge.numSetVars
      edgeSum += edge.numFreeIntVars
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
    println("Edge sizes    : " + edgeSizes.mkString("{", ", ", "}"))
    println("Set variables : " + setVars.mkString("{", ", ", "}"))
    println
  }


  /* Model construction */

  import scala.collection.mutable.{BitSet => MutableBitSet, StringBuilder}

  val mkSingleton: Z3FuncDecl
  val mkCard: Z3FuncDecl


  def toBapaModel(z3model: Z3Model): BAPAModel = {
    
    case class Node(label: BitSet, regions: MutableMap[BitSet,Int]) {
      var parent : Node = null
      val neighbors = new MutableSet[Node]()
      val content = new MutableMap[BitSet,MutableSet[Int]]()
      
      override def hashCode = label.hashCode
      
      override def equals(that: Any) =
        (that != null &&
            that.isInstanceOf[Node] &&
            that.asInstanceOf[Node].label == this.label)
      
      def addNeighbor(node: Node) {
        if (node != this) {
          this.neighbors += node
          node.neighbors += this
        }
      }
      
      def name = (label map mkName).mkString
      
      override def toString = {
        "Node " + name +
        " parent = " + (if (parent == null) "null" else parent.name) +
        " neighbors = " + (neighbors map {_.name})
      }
    }
      
    val cache = new MutableMap[BitSet,Option[Node]]()
    val nodeOrder = new ArrayBuffer[Node]()
    var errorVennRegion: String = null

    // Read model for venn regions and add them to the cache
    def bubbleToNode(bubble: AbstractBubble) = cache getOrElse(bubble.label, {
        var regions = new MutableMap[BitSet,Int]()
        def indexToIDset(index: Int): BitSet = {
          val idset = MutableBitSet()
          for (i <- 0 until bubble.numSetVars; if (index & (1 << i)) != 0) {
            idset += bubble.ids(i)
          }
          idset
        }
        var failure = false
        for (i <- 0 until bubble.numVennRegions) {
          z3model.evalAs[Int](bubble.vennRegions(i).ast) match {
            case Some(size) =>
              if (size > 0) {
                val ids = indexToIDset(i)
                regions(ids) = size
              }
            case None =>
              failure = true
              if (errorVennRegion == null) {
                errorVennRegion = "evalAs[Int] on venn region failed ! " + bubble.vennRegions(i).ast
              }
          }
        }
        val result = if (failure) None else Some(Node(bubble.label, regions))
        cache(bubble.label) = result
//         if (bubble.isInstanceOf[Bubble]) print("Bubble ") else print("Edge ")
//         println((bubble.label map mkName).mkString + " => " + result.toString)
        result
    })
    // Initialize data structures
    def init {
      // (Try to) read sizes of venn regions and build the new tree
      for (bubble <- Universe.allBubbles.values; bnode <- bubbleToNode(bubble); edge <- bubble.edges; enode <- bubbleToNode(edge)) {
        bnode addNeighbor enode
      }
      // Build ordering over the new tree
      val seen = new MutableSet[Node]()
      def dfs(from: Node) {
        seen += from
        var stack = List(from)
        while (stack.nonEmpty) {
          val node = stack.head
          stack = stack.tail
          nodeOrder += node
          for (next <- node.neighbors; if !seen(next)) {
            seen(next) = true
            next.parent = node
            stack = next :: stack
          }
        }
      }
      for (opt <- cache.values; node <- opt) if (!seen(node)) dfs(node)
    }
    // Create a set of representative integers for each venn region
    def populate {
      var lastInt = 0
      def nextInt = {
        lastInt += 1
        lastInt
      }
      def nextSeq(size: Int) = {
        val temp = lastInt + 1
        lastInt += size
        new MutableSet() ++ (temp to lastInt)
      } 
      def fillInitial(node: Node) {
        for ((reg, size) <- node.regions) {
          node.content(reg) = nextSeq(size)
        }
      }
      def fillNext(from: Node, to: Node) {
        val copiedRegions = new MutableMap[BitSet,Int]() ++ to.regions
        for ((reg2, _) <- copiedRegions) to.content(reg2) = new MutableSet[Int]()
        for ((reg, set) <- from.content; elem <- set) {
          val relevant = reg & to.label
          def matches(entry: (BitSet,Int)) = (entry._1 & from.label) == relevant
          copiedRegions find matches match {
            case None => error("Uuh, this is bad...")
            case Some((reg2, size)) =>
              to.content(reg2) += elem
              if (size > 1) {
                copiedRegions(reg2) = size - 1
              } else {
                copiedRegions -= reg2
                require(size == 1)
              }
          }
        }
      }
      for (node <- nodeOrder) {
        if (node.parent == null) fillInitial(node)
        else fillNext(node.parent, node)
      }
    }
    // Reconstruct sets from venn regions
    def reconstruct = {
      val recons = new MutableMap[Int,MutableSet[Int]]()
      for (node <- nodeOrder; setID <- node.label) {
        val set = new MutableSet[Int]()
        for ((reg, elems) <- node.content; if reg(setID)) set ++= elems
//         println(mkName(setID) +  " = " + set + " because " + node)
        if (recons contains setID) {
          if (recons(setID) != set) {
            // DEBUG: assertion failed
//             printDebug
            error("Inconsistent set " + mkSym(setID) + " aka " + mkName(setID) + "  " +
              set + " != " + recons(setID))
          }
        } else {
          recons(setID) = set
        }
      }
//       for ((setID, set) <- recons) {
//             println("Set " + mkSym(setID) + " aka " + mkName(setID) + " : " + set)
//       }
//       println(recons)
      recons
    }
    // Evalute cardinality as integer
    def evalAsBapaInt(ast: Z3AST) = z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkCard =>
        val ast2 = treeToZ3(BubbleBapaToPaTranslator(z3ToTree(ast)))
        z3model.evalAs[Int](ast2)
      case _ => None
    }
    // DEBUG: print stuff
    def printDebug {
      println("=== Nodes ===")
      for (node <- nodeOrder) {
        println(node)
        for ((bits, set) <- node.content) {
          println("   " + (idToName(bits).mkString) + " -> " + set)
        }
      }
      println("=== Hyper tree ===")
      Universe.showState
    }
    // rename elements such that singletons sets have a correct representation
    def singletons(recons: MutableMap[Int,MutableSet[Int]]) = {
      val map = new MutableMap[Int,Int]()
      val rev = new MutableMap[Int,Int]()
      def rename(i: Int) = map getOrElse(i, i)
      def reverse(i: Int) = rev getOrElse(i, i)
      
      for ((setID, content) <- recons) {
        z3.getASTKind(mkSym(setID).ast) match {
          case Z3AppAST(decl, args) if decl == mkSingleton =>
            val evaluated = z3model.evalAs[Int](args(0))
            (if (evaluated.isEmpty) evalAsBapaInt(args(0)) else evaluated) match {
              case Some(rElem) =>
                require(recons(setID).size == 1)
                val lCurrent = recons(setID).iterator.next
//                 println(mkSym(setID).ast + "  " + lCurrent + "  ->  " + rElem)
                val rCurrent = rename( lCurrent )
                val lElem = reverse( rElem )
                if (rCurrent != rElem) {
                  map(lCurrent) = rElem
                  map(lElem) = rCurrent
                  rev(rCurrent) = lElem
                  rev(rElem) = lCurrent
//                   for ((i,j) <- map)  println(i+ " -> " + j)
                }
              case None =>
                println("WARNING : evalAs[Int] on singleton element failed ! " + mkSym(setID).ast )
//                 for (ast <- getEqClassMembers(args(0))) println("> " + ast)
            }
          case _ =>
        }
      } 
//       for ((i,j) <- map)  println(i+ " -> " + j)
      recons map  { case (id,ctnt) => {
//         println(mkSym(id).toString + "   " + ctnt + "  ->  " + (ctnt map rename))
        (id, ctnt map rename)
      }}
    }
    // Create model object
    def toModel(recons: MutableMap[Int,MutableSet[Int]]) = {
      val blacklist = new MutableSet[Z3AST]()
      for ((_, venn) <- cachedRegions) blacklist += venn.ast
      val result = MutableMap[Z3AST,Set[Int]]()
      for ((id, set) <- recons) result(mkSym(id).ast) = set.toSet
      BAPAModel(z3model, result.toMap, blacklist.toSet, null)
    }
    try {
      init
      populate
  //     printDebug
  //     Universe.showState
  //     nodeOrder foreach println
      toModel(singletons(reconstruct))
    } catch {
      case ex: Throwable =>
        var err = ex.toString
        if (errorVennRegion != null) err += "\nPossible cause :\n  " + errorVennRegion
        BAPAModel(z3model, Map.empty[Z3AST,Set[Int]], Set.empty[Z3AST], err)
    }
  }
//   def getEqClassMembers(ast: Z3AST) : Iterator[Z3AST]
}

/* Bapa model class */

case class BAPAModel(z3model: Z3Model, setModel: Map[Z3AST,Set[Int]], blacklist: Set[Z3AST], error: String = null) {

  def evalAsIntSet(ast: Z3AST) = setModel get ast

  override def toString = {
    val buf = new StringBuilder()
    // Z3 model
    /*
    val temp = new ArrayBuffer[(String,String)]()
    for (decl <- z3model.getConstants) {
      val app = decl()
      if (!blacklist(app)) z3model eval app match {
        case None =>
        case Some(ast) =>
          temp += app.toString -> ast.toString
      }
    }
    temp sortWith {_._1 < _._1}
    val max1 = (temp foldLeft 0){(a,b) => scala.math.max(a, b._1.size)}
    for ((name, value) <- temp) {
      val n = max1 - name.size
      buf ++= "  " + name + (" " * n) +"  ->  " + value + "\n"
    }
    */
    // TODO: HACK ! (scalaZ3 interface has no model navigation yet)
    val badstart = blacklist map {_.toString}
    val lines = (z3model.toString split '\n').toList filterNot {line =>
      badstart exists {line startsWith _}
    }
    buf ++= "Z3 model :\n"
    for (line <- lines) {
      buf ++= "  "
      buf ++= line
      buf += '\n'
    }
    // BAPA model
    if (error == null) {
      def format(pair: (Z3AST, Set[Int])): (String, String) = (pair._1.toString, pair._2.toList.sortWith{_ < _}.mkString("{ "," "," }"))
      val pairs =  (setModel.toList map format) sortWith {_._1 < _._1}
      val max2 = (pairs foldLeft 0){(a,b) => scala.math.max(a, b._1.size)}
      buf ++= "BAPA model :\n"
      for ((name, set) <- pairs) {
        val n = max2 - name.size
        buf ++= "  "
        buf ++= name
        buf ++= " " * n
        buf ++= "  ->  "
        buf ++= set
        buf += '\n'
      }
    } else {
      buf ++= "An error occurred while creating the BAPA model :\n  "
      buf ++= error
    }
    buf.toString
  }
}
