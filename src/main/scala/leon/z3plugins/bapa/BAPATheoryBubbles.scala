/* Copyright 2009-2013 EPFL, Lausanne */

package purescala.z3plugins.bapa

import scala.collection.mutable.{Stack, ArrayBuffer, Set => MutableSet, HashMap => MutableMap}
import scala.collection.immutable.{Map => ImmutableMap}
import z3.scala._
import AST._
import NormalForms.{simplify, setVariables, rewriteSetRel}

import scala.sys.error

class BAPATheoryBubbles(val z3: Z3Context) extends Z3Theory(z3, "BAPATheory (bubbles)") with Bubbles {

  /* Flags */

//   private val WITH_Z3_SET_AXIOMS = true
  private val WITH_Z3_SET_AXIOMS = false

  private val SINGLETON_DISEQUALITIES = true // theory is incomplete otherwise
//   private val SINGLETON_DISEQUALITIES = false
  
  /* Register callbacks */

  setCallbacks(
    reset = true,
    restart = true,
    push = true,
    pop = true,
    reduceApp = true,
    newApp = true,
    newElem = true,
    newAssignment = true,
    newEq = true,
    newDiseq = true,
    finalCheck = true
  )
  // This makes the Theory Proxy print out all calls that are
  // forwarded to the theory.
  //   showCallbacks(true)

  /* Theory constructs */

  val mkElemSort = z3.mkIntSort
  val mkSetSort = mkTheorySort(z3.mkStringSymbol("SetSort"))
  val mkEmptySet = mkTheoryValue(z3.mkStringSymbol("EmptySet"), mkSetSort)
  val mkSingleton = mkTheoryFuncDecl(z3.mkStringSymbol("Singleton"), Seq(mkElemSort), mkSetSort)
  val mkCard = mkUnarySetfun("Cardinality", z3.mkIntSort)
  val mkSubsetEq = mkBinarySetfun("SubsetEq", z3.mkBoolSort)
  val mkElementOf = mkTheoryFuncDecl(z3.mkStringSymbol("IsElementOf"), Seq(mkElemSort, mkSetSort), z3.mkBoolSort)
  val mkUnion = mkBinarySetfun("Union", mkSetSort)
  val mkIntersect = mkBinarySetfun("Intersect", mkSetSort)
  val mkComplement = mkUnarySetfun("Complement", mkSetSort)

  private[bapa] val mkDomainSize = z3.mkFreshConst("DomainSize", z3.mkIntSort)
  // This function returns the single element for singletons, and is uninterpreted otherwise.
  private[bapa] val mkAsElement = mkUnarySetfun("AsElement", z3.mkIntSort)
  private[bapa] val mkZ3SetSort = z3.mkSetSort(mkElemSort)
  private[bapa] val mkAsBAPA = mkTheoryFuncDecl(z3.mkStringSymbol("asBAPA"), Seq(mkZ3SetSort), mkSetSort)
  
  def mkDisjoint(set1: Z3AST, set2: Z3AST) =
    z3.mkEq(mkIntersect(set1, set2), mkEmptySet)

  def mkDifference(set1: Z3AST, set2: Z3AST) =
    mkIntersect(set1, mkComplement(set2))

  def mkConst(name: String) = mkTheoryConstant(z3.mkStringSymbol(name), mkSetSort)

  private var freshCounter = 0

  def mkFreshConst(name: String) = {
    freshCounter += 1
    mkConst(name + "." + freshCounter)
  }

  private def mkUnarySetfun(name: String, rType: Z3Sort) =
    mkTheoryFuncDecl(z3.mkStringSymbol(name), Seq(mkSetSort), rType)

  private def mkBinarySetfun(name: String, rType: Z3Sort) =
    mkTheoryFuncDecl(z3.mkStringSymbol(name), Seq(mkSetSort, mkSetSort), rType)

  /* Theory stack */

  private val bubbleStack = new Stack[(Int,Bubble)]()

  private sealed abstract class Clause
  private case class CardClause(tree: Tree) extends Clause
  private case class SingletonClause(tree: Tree) extends Clause
  private case class AssignClause(tree: Tree, polarity: Boolean) extends Clause
  private case class EqClause(tree1: Tree, tree2: Tree) extends Clause
  private case class DiseqClause(tree1: Tree, tree2: Tree) extends Clause

  private def addClause(clause: Clause) {
    assertClause(clause)
  }

  /* Axiom assertion helper functions */
  
  private def assertAxiomNow(axiom: Z3AST) {
    //     println(axiom)
    assertAxiom(axiom)
  }

  protected def assertAxiomSafe(axiom: Z3AST) {
    if (canAssertAxiom) {
      assertAxiomNow(axiom)
    } else {
      // Assert axiom eventually
      axiomsToAssert += ((pushLevel, axiom))
    }
    //     println("> Asserting: " + axiom)
  }

  // We use this trick to circumvent the fact that you (apparently) can't
  // assertAxioms with some callbacks, such as newApp...
  private val axiomsToAssert: MutableSet[(Int, Z3AST)] = MutableSet.empty
  private var pushLevel = 0
  private var canAssertAxiom = false

  private def safeBlockToAssertAxioms[A](block: => A): A = {
    canAssertAxiom = true;
    {
      // Assert all remaining axioms
      if (axiomsToAssert.nonEmpty) {
        val toPreserve: MutableSet[(Int, Z3AST)] = MutableSet.empty
        
        for ((lvl, ax) <- axiomsToAssert) {
          // println("Asserting eventual axiom: " + ax)
          assertAxiomNow(ax)
          if (lvl < pushLevel)
            toPreserve += ((lvl, ax))
        }
        axiomsToAssert.clear
        axiomsToAssert ++= toPreserve
      }
    }
    val result = block
    canAssertAxiom = false
    result
  }

  /* Callbacks */

  def init {
    pushLevel = 0
    //     push
  }
  init

  override def reset {
    init
  }

  override def restart {
    init
  }

  override def push {
    pushLevel += 1
  }

  override def pop {
    pushLevel -= 1
    while (bubbleStack.nonEmpty && bubbleStack.head._1 > pushLevel) {
      Universe removeBubble bubbleStack.pop._2
    }
  }

  override def reduceApp(fd: Z3FuncDecl, args: Z3AST*): Option[Z3AST] = {
    if (fd == mkCard) {
      if (args(0) == mkEmptySet) {
        Some(z3.mkInt(0, z3.mkIntSort))
      } else {
        None
      }
    } else if (fd == mkSubsetEq) {
      if (args(0) == mkEmptySet) {
        Some(z3.mkTrue)
      } else if (args(1) == mkEmptySet) {
        Some(z3.mkEq(mkEmptySet, args(0)))
      } else {
        None
      }
    } else if (fd == mkElementOf) {
      val elem = args(0)
      val set = args(1)
      if (set == mkEmptySet) {
        Some(z3.mkFalse)
      } else {
        Some(mkSubsetEq(mkSingleton(elem), set))
      }
    } else {
      None
    }
  }

  override def newElem(ast1: Z3AST) {
    def asSingleton(ast: Z3AST) = z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkSingleton => Some(args(0))
      case _ => None
    }
    if (SINGLETON_DISEQUALITIES) asSingleton(ast1) match {
      case None =>
      case Some(elem1) =>
        for (ast2 <- getElems; if ast2 != ast1) asSingleton(ast2) match {
          case None =>
          case Some(elem2) =>
            val bapaTree = !(z3ToTree(ast1) seteq z3ToTree(ast2))
            val paTree = BubbleBapaToPaTranslator(bapaTree)
            assertAxiomSafe(z3.mkImplies(
              z3.mkDistinct(elem1, elem2),
              treeToZ3(paTree)
            ))
        }
    }
    // Connection to Z3 sets
    if (WITH_Z3_SET_AXIOMS) addSetExpression(ast1)
  }

  override def newApp(ast: Z3AST) {
    z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkCard =>
        addClause(CardClause(z3ToTree(ast)))
        assertAxiomSafe(z3.mkIff(
          z3.mkEq(ast, z3.mkInt(0, z3.mkIntSort)),
          z3.mkEq(args(0), mkEmptySet)
        ))
      case Z3AppAST(decl, args) if decl == mkSingleton =>
        addClause(SingletonClause(z3ToTree(ast)))
        assertAxiomSafe(z3.mkEq(mkAsElement(ast), args(0)))
        assertAxiomSafe(z3.mkEq(mkCard(ast), z3.mkInt(1, z3.mkIntSort)))
      case _ =>
    }
    // Connection to Z3 sets
    if (WITH_Z3_SET_AXIOMS) addSetExpression(ast)
  }

  override def newAssignment(ast: Z3AST, polarity: Boolean): Unit = safeBlockToAssertAxioms {
    /*
    if(polarity) {
      z3.getASTKind(ast) match {
        case Z3AppAST(decl, args) if decl == mkSubsetEq =>
          inclusionStack push (inclusionStack.pop newSubsetEq (args(0), args(1)))
        case _ => 
      }
    }
    */
    addClause(AssignClause(z3ToTree(ast), polarity))
  }

  override def newEq(ast1: Z3AST, ast2: Z3AST): Unit = safeBlockToAssertAxioms {
    if (z3.getSort(ast1) == mkSetSort && !(WITH_Z3_SET_AXIOMS && (isAsBapa(ast1) || isAsBapa(ast2)))) {
      /*
      inclusionStack.push(inclusionStack.pop.newEq(ast1, ast2))
      */
      // S = {} implies the following for sets T in the equivalence class of S
      // -  |T| = 0
      // -  T ++ U = U
      // -  U ++ T = U
      // -  T ** U = {}
      // -  U ** T = {}
      if (ast1 == mkEmptySet || ast2 == mkEmptySet) {
        val nonEmpty = if (ast1 == mkEmptySet) ast2 else ast1
        for (congruent <- getEqClassMembers(nonEmpty)) {
          for (parent <- getParents(congruent)) {
            z3.getASTKind(parent) match {
              case Z3AppAST(decl, args) if decl == mkCard && args(0) == congruent =>
                assertAxiomSafe(z3.mkIff(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(parent, z3.mkInt(0, z3.mkIntSort))))
//                   z3.mkEq(mkCard(congruent), z3.mkInt(0, z3.mkIntSort))))
              case Z3AppAST(decl, args) if decl == mkUnion && args(0) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(parent, args(1))))
//                   z3.mkEq(mkUnion(congruent, args(1)), args(1))))
              case Z3AppAST(decl, args) if decl == mkUnion && args(1) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(parent, args(0))))
//                   z3.mkEq(mkUnion(args(0), congruent), args(0))))
              case Z3AppAST(decl, args) if decl == mkIntersect && args(0) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(parent, mkEmptySet)))
//                   z3.mkEq(mkUnion(congruent, args(1)), mkEmptySet)))
              case Z3AppAST(decl, args) if decl == mkIntersect && args(1) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(parent, mkEmptySet)))
//                   z3.mkEq(mkUnion(args(0), congruent), mkEmptySet)))
              case _ =>
            }
          }
        }
      }
      addClause(EqClause(z3ToTree(ast1), z3ToTree(ast2)))
    }
  }

  override def newDiseq(ast1: Z3AST, ast2: Z3AST): Unit = safeBlockToAssertAxioms {
    if (z3.getSort(ast1) == mkSetSort) {
      if (WITH_Z3_SET_AXIOMS && (isAsBapa(ast1) || isAsBapa(ast2))) return ()
      // S != {} implies |T| > 0 for all sets T in the equivalence class of S
      if (ast1 == mkEmptySet || ast2 == mkEmptySet) {
        val nonEmpty = if (ast1 == mkEmptySet) ast2 else ast1
        for (congruent <- getEqClassMembers(nonEmpty)) {
          for (parent <- getParents(congruent)) {
            z3.getASTKind(parent) match {
              case Z3AppAST(decl, args) if decl == mkCard && args(0) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkDistinct(congruent, mkEmptySet),
                  z3.mkGT(parent, z3.mkInt(0, z3.mkIntSort))))
//                   z3.mkGT(mkCard(congruent), z3.mkInt(0, z3.mkIntSort))))
              case _ =>
            }
          }
        }
      }
      addClause(DiseqClause(z3ToTree(ast1), z3ToTree(ast2)))
    } else {
      /*
      val set1 = mkSingleton(ast1)
      val set2 = mkSingleton(ast2)
      if (SINGLETON_DISEQUALITIES && (getElems contains set1) && (getElems contains set2)) {
        val bapaTree = (z3ToTree(set1) seteq z3ToTree(set2))
        val paTree = BubbleBapaToPaTranslator(bapaTree)
        assertAxiomSafe(z3.mkIff(
          treeToZ3(paTree),
          z3.mkEq(ast1, ast2)
        ))
      }
      */
    }
  }

  override def finalCheck: Boolean = safeBlockToAssertAxioms {
    //     println("==== Bubbles at final check ====")
    //     Universe.showState
    //     println("================================")
    true
  }

  /* Transformations */

  def treeToZ3(tree: Tree): Z3AST = tree match {
    case Var(sym) => sym.ast
    case Lit(TrueLit) => z3.mkTrue
    case Lit(FalseLit) => z3.mkFalse
    case Lit(IntLit(i)) => z3.mkInt(i, z3.mkIntSort)
    case Op(AND, ts) => z3.mkAnd((ts map treeToZ3): _*)
    case Op(OR, ts) => z3.mkOr((ts map treeToZ3): _*)
    case Op(NOT, Seq(t)) => z3.mkNot(treeToZ3(t))
    case Op(IFF, Seq(t1, t2)) => z3.mkIff(treeToZ3(t1), treeToZ3(t2))
    case Op(EQ, Seq(t1, t2)) => z3.mkEq(treeToZ3(t1), treeToZ3(t2))
    case Op(LT, Seq(t1, t2)) => z3.mkLT(treeToZ3(t1), treeToZ3(t2))
    case Op(ADD, ts) => z3.mkAdd((ts map treeToZ3): _*)
    case Op(CARD, Seq(t)) => mkCard(treeToZ3(t))
    case Op(SETEQ, Seq(t1, t2)) => z3.mkEq(treeToZ3(t1), treeToZ3(t2))
    case Op(SUBSETEQ, Seq(t1, t2)) => mkSubsetEq(treeToZ3(t1), treeToZ3(t2))
    case Op(UNION, ts) => mkUnion((ts map treeToZ3): _*)
    case Op(INTER, ts) => mkIntersect((ts map treeToZ3): _*)
    case Op(COMPL, Seq(t)) => mkComplement(treeToZ3(t))
    case Lit(EmptySetLit) => mkEmptySet
    case _ => error("Unsupported conversion from BAPA-tree to Z3AST :\n" + tree)
  }

  def z3ToTree(ast: Z3AST): Tree = {
    if (ast == mkEmptySet) EmptySet
    else z3.getASTKind(ast) match {
      case Z3AppAST(decl, Nil) => SetSymbol(ast)
      case Z3AppAST(decl, args) if decl == mkSubsetEq => Op(SUBSETEQ, args map z3ToTree)
      case Z3AppAST(decl, args) if decl == mkUnion => Op(UNION, args map z3ToTree)
      case Z3AppAST(decl, args) if decl == mkIntersect => Op(INTER, args map z3ToTree)
      case Z3AppAST(decl, args) if decl == mkComplement => Op(COMPL, args map z3ToTree)
      case Z3AppAST(decl, args) if decl == mkCard => Op(CARD, Seq(z3ToTree(args(0))))
      case Z3AppAST(decl, args) if decl == mkAsBAPA =>
        if (!(asBapaToBapa contains ast)) {
          for ((asB, b) <- asBapaToBapa)  println(asB + "  ->  " + b)
          error("Could not find : \n" + ast)
        }
        z3ToTree(asBapaToBapa(ast))
      case _ => SetSymbol(ast)
    }
  }

  /* Interaction with Z3 sets */

  private val asBapaToBapa = new MutableMap[Z3AST,Z3AST]()
  private val cachedBapaToAsBapa = new MutableMap[Z3AST,Z3AST]()
  private val cachedBapaVarToZ3set = new MutableMap[Z3AST,Z3AST]()

  def addSetExpression(ast: Z3AST) {
    if (z3.getSort(ast) == mkSetSort) z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkAsBAPA =>
        // Not needed
//         println("Not needed : " + ast)
      case _ if cachedBapaToAsBapa contains ast =>
        // Already added
//         println("Already added : " + ast)
      case _ =>
        val axiom = z3.mkEq(ast, bapaSetToAsBapa(ast))
//         println("Axiom : " + axiom)
        assertAxiomSafe(axiom)
    }
  }

  private def bapaSetToAsBapa(ast: Z3AST) = {
//     var level = 0
    def toZ3set(ast: Z3AST): Z3AST = {
//       level += 1
//       println(("  " * level) + "translating " + ast)
      val res = if (ast == mkEmptySet) z3.mkEmptySet(mkElemSort)
      else z3.getASTKind(ast) match {
        case Z3AppAST(decl, Nil) =>
          mkZ3SetVar(ast)
        case Z3AppAST(decl, args) if decl == mkSubsetEq =>
          z3.mkSetSubset(toZ3set(args(0)), toZ3set(args(1)))
        case Z3AppAST(decl, args) if decl == mkUnion =>
          z3.mkSetUnion(toZ3set(args(0)), toZ3set(args(1)))
        case Z3AppAST(decl, args) if decl == mkIntersect =>
          z3.mkSetIntersect(toZ3set(args(0)), toZ3set(args(1)))
        case Z3AppAST(decl, args) if decl == mkComplement =>
          z3.mkSetComplement(toZ3set(args(0)))
        case Z3AppAST(decl, args) if decl == mkSingleton =>
          z3.mkSetAdd(z3.mkEmptySet(mkElemSort), args(0))
        case Z3AppAST(decl, args) if decl == mkAsBAPA =>
          args(0)
        case _ =>
          mkZ3SetVar(ast)
        }
//       println(("  " * level) + "result " + res)
//       level -= 1
      res
    }
    cachedBapaToAsBapa getOrElse(ast, {
      val asBapa = mkAsBAPA(toZ3set(ast))
      cachedBapaToAsBapa(ast) = asBapa
      asBapaToBapa(asBapa) = ast
      asBapa
    })
  }

  private def mkZ3SetVar(ast: Z3AST) = cachedBapaVarToZ3set getOrElse(ast, {
    val fresh = z3.mkFreshConst("z3twin", mkZ3SetSort)
    cachedBapaVarToZ3set(ast) = fresh
    fresh
  })

  private def isAsBapa(ast: Z3AST) = z3.getASTKind(ast) match {
    case Z3AppAST(decl, args) if decl == mkAsBAPA => true
    case _ => false
  }

  /* PA translation */

  def BubbleBapaToPaTranslator(tree0: Tree) = {
    val tree1 = simplify(tree0)
    val (myBubble, isNew) = Universe addBubble setVariables(tree1)
    if (isNew) bubbleStack push ((pushLevel, myBubble))
    def rec(tree: Tree): Tree = tree match {
      case Op(CARD, Seq(set)) => myBubble translate set
      case Op(op, ts) => Op(op, ts map rec)
      case Var(_) | Lit(_) => tree
    }
    simplify(rec(simplify(rewriteSetRel(tree1))))
  }

  private def assertClause(clause: Clause) = clause match {
    case CardClause(bapaTree) =>
      val paTree = BubbleBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkEq(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
      ))
    case SingletonClause(tree) =>
      // nothing to do (except optimizations :P)
    case AssignClause(tree, polarity) =>
      val bapaTree = if (polarity) tree else !tree
      val paTree = BubbleBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkImplies(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
      ))
    case EqClause(tree1, tree2) =>
      val bapaTree = tree1 seteq tree2
      val paTree = BubbleBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkImplies(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
      ))
    case DiseqClause(tree1, tree2) =>
      val bapaTree = !(tree1 seteq tree2)
      val paTree = BubbleBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkImplies(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
      ))
  }
}
