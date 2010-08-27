package purescala.z3plugins.bapa

import scala.collection.mutable.{Stack, ArrayBuffer, Set => MutableSet}
import scala.collection.immutable.{Map => ImmutableMap}
import z3.scala._
import AST._
import NormalForms.{simplify, setVariables, rewriteSetRel}

class BAPATheoryBubbles(val z3: Z3Context) extends Z3Theory(z3, "BAPATheory (bubbles)") with Bubbles {

  /* Register callbacks */

  setCallbacks(
    reset = true,
    restart = true,
    push = true,
    pop = true,
    reduceApp = true,
    newApp = true,
    newAssignment = true,
    newEq = true,
    newDiseq = true,
    finalCheck = true
    )
  // This makes the Theory Proxy print out all calls that are
  // forwarded to the theory.
  //   showCallbacks(true)

  /* Theory constructs */

  val mkSetSort = mkTheorySort(z3.mkStringSymbol("SetSort"))
  val mkEmptySet = mkTheoryValue(z3.mkStringSymbol("EmptySet"), mkSetSort)
  val mkSingleton = mkTheoryFuncDecl(z3.mkStringSymbol("Singleton"), Seq(z3.mkIntSort), mkSetSort)
  val mkCard = mkUnarySetfun("Cardinality", z3.mkIntSort)
  val mkSubsetEq = mkBinarySetfun("SubsetEq", z3.mkBoolSort)
  val mkElementOf = mkTheoryFuncDecl(z3.mkStringSymbol("IsElementOf"), Seq(z3.mkIntSort, mkSetSort), z3.mkBoolSort)
  val mkUnion = mkBinarySetfun("Union", mkSetSort)
  val mkIntersect = mkBinarySetfun("Intersect", mkSetSort)
  val mkComplement = mkUnarySetfun("Complement", mkSetSort)

  private[bapa] val mkDomainSize = z3.mkFreshConst("DomainSize", z3.mkIntSort)
  // This function returns the single element for singletons, and is uninterpreted otherwise.
  private[bapa] val mkAsElement = mkUnarySetfun("AsElement", z3.mkIntSort)

  def mkDisjoint(set1: Z3AST, set2: Z3AST) =
    z3.mkEq(mkIntersect(set1, set2), mkEmptySet)

  def mkDifference(set1: Z3AST, set2: Z3AST) =
    mkIntersect(set1, mkComplement(set2))

  private var freshCounter = 0

  def mkConst(name: String) = mkTheoryConstant(z3.mkStringSymbol(name), mkSetSort)

  def mkFreshConst(name: String) = {
    freshCounter += 1
    mkConst(name + "." + freshCounter)
  }

  private def mkUnarySetfun(name: String, rType: Z3Sort) =
    mkTheoryFuncDecl(z3.mkStringSymbol(name), Seq(mkSetSort), rType)

  private def mkBinarySetfun(name: String, rType: Z3Sort) =
    mkTheoryFuncDecl(z3.mkStringSymbol(name), Seq(mkSetSort, mkSetSort), rType)

  /* Theory stack */

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
  def assertAxiomNow(axiom: Z3AST) {
    //     println(axiom)
    assertAxiom(axiom)
  }

  def assertAxiomSafe(axiom: Z3AST) {
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

  override def newApp(ast: Z3AST) {
    z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkCard =>
        addClause(CardClause(z3ToTree(ast)))
        assertAxiomSafe(z3.mkIff(z3.mkEq(ast, z3.mkInt(0, z3.mkIntSort)), z3.mkEq(args(0), mkEmptySet)))
      case Z3AppAST(decl, args) if decl == mkSingleton =>
        addClause(SingletonClause(z3ToTree(ast)))
        assertAxiomSafe(z3.mkEq(mkAsElement(ast), args(0)))
        assertAxiomSafe(z3.mkEq(mkCard(ast), z3.mkInt(1, z3.mkIntSort)))
      case _ =>
    }
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
    if (z3.getSort(ast1) == mkSetSort) {
      /*
      inclusionStack.push(inclusionStack.pop.newEq(ast1, ast2))
      */
      if (ast1 == mkEmptySet || ast2 == mkEmptySet) {
        val nonEmpty = if (ast1 == mkEmptySet) ast2 else ast1
        for (congruent <- getEqClassMembers(nonEmpty)) {
          for (parent <- getParents(congruent)) {
            z3.getASTKind(parent) match {
              case Z3AppAST(decl, args) if decl == mkCard && args(0) == congruent =>
                assertAxiomSafe(z3.mkIff(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkCard(congruent), z3.mkInt(0, z3.mkIntSort))))
              case Z3AppAST(decl, args) if decl == mkUnion && args(0) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(congruent, args(1)), args(1))))
              case Z3AppAST(decl, args) if decl == mkUnion && args(1) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(args(0), congruent), args(0))))
              case Z3AppAST(decl, args) if decl == mkIntersect && args(0) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(congruent, args(1)), mkEmptySet)))
              case Z3AppAST(decl, args) if decl == mkIntersect && args(1) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(args(0), congruent), mkEmptySet)))
              case _ =>;
            }
          }
        }
      }
      addClause(EqClause(z3ToTree(ast1), z3ToTree(ast2)))
    }
  }

  override def newDiseq(ast1: Z3AST, ast2: Z3AST): Unit = safeBlockToAssertAxioms {
    if (z3.getSort(ast1) == mkSetSort) {
      if (ast1 == mkEmptySet || ast2 == mkEmptySet) {
        val nonEmpty = if (ast1 == mkEmptySet) ast2 else ast1
        for (congruent <- getEqClassMembers(nonEmpty)) {
          for (parent <- getParents(congruent)) {
            z3.getASTKind(parent) match {
              case Z3AppAST(decl, args) if decl == mkCard && args(0) == congruent =>
                assertAxiomSafe(z3.mkImplies(
                  z3.mkDistinct(congruent, mkEmptySet),
                  z3.mkGT(mkCard(congruent), z3.mkInt(0, z3.mkIntSort))))
              case _ =>
            }
          }
        }
      }
      addClause(DiseqClause(z3ToTree(ast1), z3ToTree(ast2)))
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
      case _ => SetSymbol(ast)
    }
  }

  def BubbleBapaToPaTranslator(tree0: Tree) = {
    val tree1 = simplify(tree0)
    val myBubble = Universe addBubble setVariables(tree1)
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
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
    case EqClause(tree1, tree2) =>
      val bapaTree = tree1 seteq tree2
      val paTree = BubbleBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
    case DiseqClause(tree1, tree2) =>
      val bapaTree = !(tree1 seteq tree2)
      val paTree = BubbleBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
  }
}
