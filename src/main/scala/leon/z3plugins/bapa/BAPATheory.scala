/* Copyright 2009-2013 EPFL, Lausanne */

/********************************************************************

   WARNING : THIS VERSION IS NOT USED (AND CERTAINLY NOT MAINTAINED).
   SEE BAPATheoryBubbles INSTEAD !

   ******************************************************************/

package purescala.z3plugins.bapa

import scala.collection.mutable.Stack
import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.{Map => ImmutableMap}
import z3.scala._
import AST._
import NormalForms.{simplify, rewriteSetRel, setVariables, purify}

import scala.sys.error

class BAPATheory(val z3: Z3Context) extends Z3Theory(z3, "BAPATheory") with VennRegions { //with InclusionGraphs {

  /* Register callbacks */

  setCallbacks(
    reduceApp = true,
    finalCheck = true,
    push = true,
    pop = true,
    newApp = true,
    newAssignment = true,
    newEq = true,
    newDiseq = true,
    reset = true,
    restart = true
    )

  // This makes the Theory Proxy print out all calls that are
  // forwarded to the theory.
  showCallbacks(true)

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

  private var freshCounter = 0

  def mkSetConst(name: String) = mkTheoryConstant(z3.mkStringSymbol(name), mkSetSort)

  def mkFreshConst(name: String) = {
    freshCounter += 1
    mkSetConst(name + "." + freshCounter)
  }

  private def mkUnarySetfun(name: String, rType: Z3Sort) =
    mkTheoryFuncDecl(z3.mkStringSymbol(name), Seq(mkSetSort), rType)

  private def mkBinarySetfun(name: String, rType: Z3Sort) =
    mkTheoryFuncDecl(z3.mkStringSymbol(name), Seq(mkSetSort, mkSetSort), rType)

  /* Theory stack */

  private val universeStack = new Stack[Universe]
  // private val inclusionStack = new Stack[InclusionGraph]

  def assertAxiomFromVennRegions(ast: Z3AST) {
    // println("Asserting: " + ast)
    assertAxiom(ast)
  }

  def assertAxiom2(ast: Z3AST) {
    // println("Asserting: " + ast)
    assertAxiom(ast)
  }

  def assertAxiomSafe(ast: Z3AST) {
    // println("Asserting: " + ast)
    assertAxiomEventually(ast)
  }

  // We use this trick to circumvent the fact that you (apparently) can't
  // assertAxioms with some callbacks, such as newApp...
  private val axiomsToAssert: MutableSet[(Int, Z3AST)] = MutableSet.empty

  protected def assertAxiomEventually(axiom: Z3AST) = {
    axiomsToAssert += ((pushLevel, axiom))
  }

  private def assertAllRemaining: Unit = {
    if (axiomsToAssert.nonEmpty) {
      val toPreserve: MutableSet[(Int, Z3AST)] = MutableSet.empty

      for ((lvl, ax) <- axiomsToAssert) {
        // println("Asserting eventual axiom: " + ax)
        assertAxiom2(ax)
        if (lvl < pushLevel) toPreserve += ((lvl, ax))
      }
      axiomsToAssert.clear
      axiomsToAssert ++= toPreserve
    }
  }

  /* Callbacks */

  override def reset {
    axiomsToAssert.clear
    universeStack.clear
    // inclusionStack.clear
    universeStack push new EmptyUniverse(mkDomainSize)
    // inclusionStack push EmptyInclusionGraph()
  }
  reset

  override def restart {
    reset
  }

  private var pushLevel = 0

  override def push {
    pushLevel = pushLevel + 1
    //assertAllRemaining
    universeStack push universeStack.head
    // inclusionStack push inclusionStack.head
  }

  override def pop {
    pushLevel = pushLevel - 1
    //assertAllRemaining
    universeStack.pop
    // inclusionStack.pop
  }

  override def newAssignment(ast: Z3AST, polarity: Boolean) {
    assertAllRemaining

    // if (polarity) {
    //   z3.getASTKind(ast) match {
    //     case Z3AppAST(decl, args) if decl == mkSubsetEq => inclusionStack.push(inclusionStack.pop.newSubsetEq(args(0), args(1)))
    //     case _ =>;
    //   }
    // }

    val assumption = if (polarity) ast else z3.mkNot(ast)
    val bapaTree = if (polarity) z3ToTree(ast) else !z3ToTree(ast)
    val paTree = NaiveBapaToPaTranslator(bapaTree)
    val axiom = z3.mkIff(assumption, treeToZ3(paTree))
    assertAxiom2(axiom)
    //     println(axiom)
    //     println("New Axiom       : " + bapaTree + " implies\n" + paTree)
  }

  override def newEq(ast1: Z3AST, ast2: Z3AST) {
    assertAllRemaining

    if (z3.getSort(ast1) == mkSetSort) {
      // inclusionStack.push(inclusionStack.pop.newEq(ast1, ast2))
      // TODO: if either ast1 or ast2 is a variable => don't add it/remove it from the stack and remember congruence class
      //       println("*** new Eq : " + ast1 + "  ==  " + ast2)

      //println("Equals : " + (ast1 == ast2))
      //println("Root Equals : " + (getEqClassRoot(ast1) == getEqClassRoot(ast2)))
      //println("Ast 1 : " + ast1)
      //println("Ast 2 : " + ast2)
      //println("Ast 1 root : " + getEqClassRoot(ast1))
      //println("Ast 2 root : " + getEqClassRoot(ast2))
      //println("Ast 1 class : " + getEqClassMembers(ast1).toList.mkString(", "))
      //println("Ast 2 class : " + getEqClassMembers(ast2).toList.mkString(", "))
      //println("Ast 1 parents : " + getParents(ast1).toList.mkString(", "))
      //println("Ast 2 parents : " + getParents(ast2).toList.mkString(", "))

      if (ast1 == mkEmptySet || ast2 == mkEmptySet) {
        val nonEmpty = if (ast1 == mkEmptySet) ast2 else ast1
        for (congruent <- getEqClassMembers(nonEmpty)) {
          for (parent <- getParents(congruent)) {
            z3.getASTKind(parent) match {
              case Z3AppAST(decl, args) if decl == mkCard && args(0) == congruent =>
                assertAxiom2(z3.mkIff(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkCard(congruent), z3.mkInt(0, z3.mkIntSort))))
              case Z3AppAST(decl, args) if decl == mkUnion && args(0) == congruent =>
                assertAxiom2(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(congruent, args(1)), args(1))))
              case Z3AppAST(decl, args) if decl == mkUnion && args(1) == congruent =>
                assertAxiom2(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(args(0), congruent), args(0))))
              case Z3AppAST(decl, args) if decl == mkIntersect && args(0) == congruent =>
                assertAxiom2(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(congruent, args(1)), mkEmptySet)))
              case Z3AppAST(decl, args) if decl == mkIntersect && args(1) == congruent =>
                assertAxiom2(z3.mkImplies(
                  z3.mkEq(congruent, mkEmptySet),
                  z3.mkEq(mkUnion(args(0), congruent), mkEmptySet)))
              case _ =>;
            }
          }
        }
      }

      val assumption = z3.mkEq(ast1, ast2)
      val bapaTree = z3ToTree(ast1) seteq z3ToTree(ast2)
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      val axiom = z3.mkImplies(assumption, treeToZ3(paTree))
      assertAxiom2(axiom)
    }
  }

  override def newDiseq(ast1: Z3AST, ast2: Z3AST) {
    assertAllRemaining
    //     println("*** new Diseq : " + ast1 + "  ==  " + ast2)

    if (z3.getSort(ast1) == mkSetSort) {
      //println("Ast 1 : " + ast1)
      //println("Ast 2 : " + ast2)
      //println("Ast 1 root : " + getEqClassRoot(ast1))
      //println("Ast 2 root : " + getEqClassRoot(ast2))
      //println("Ast 1 class : " + getEqClassMembers(ast1).toList.mkString(", "))
      //println("Ast 2 class : " + getEqClassMembers(ast2).toList.mkString(", "))
      //println("Ast 1 parents : " + getParents(ast1).toList.mkString(", "))
      //println("Ast 2 parents : " + getParents(ast2).toList.mkString(", "))

      if (ast1 == mkEmptySet || ast2 == mkEmptySet) {
        val nonEmpty = if (ast1 == mkEmptySet) ast2 else ast1
        for (congruent <- getEqClassMembers(nonEmpty)) {
          for (parent <- getParents(congruent)) {
            z3.getASTKind(parent) match {
              case Z3AppAST(decl, args) if decl == mkCard && args(0) == congruent =>
                assertAxiom2(z3.mkImplies(
                  z3.mkDistinct(congruent, mkEmptySet),
                  z3.mkGT(mkCard(congruent), z3.mkInt(0, z3.mkIntSort))))
              case _ =>;
            }
          }
        }
      }

      val assumption = z3.mkDistinct(ast1, ast2)
      val bapaTree = !(z3ToTree(ast1) seteq z3ToTree(ast2))
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      val axiom = z3.mkImplies(assumption, treeToZ3(paTree))
      assertAxiom2(axiom)
    }
  }

  override def newApp(ast: Z3AST) {
    //    println("*** new App : " + ast)
    z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkCard =>
        val bapaTree = z3ToTree(ast)
        val paTree = NaiveBapaToPaTranslator(bapaTree)
        assertAxiomEventually(z3.mkEq(treeToZ3(paTree), ast))
        assertAxiomEventually(z3.mkIff(z3.mkEq(ast, z3.mkInt(0, z3.mkIntSort)), z3.mkEq(args(0), mkEmptySet)))
      case Z3AppAST(decl, args) if decl == mkSingleton =>
        assertAxiomEventually(z3.mkEq(mkAsElement(ast), args(0)))
        assertAxiomEventually(z3.mkEq(mkCard(ast), z3.mkInt(1, z3.mkIntSort)))
      case _ =>
    // ignore other functions
    }
  }

  // TODO: add reductions for union & inter (empty set) and compl (nnf ?)
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
      //    } else if (fd == mkIsSingleton) {
      //      if (args(0) == mkEmptySet) {
      //        Some(z3.mkFalse)
      //      } else {
      //        None
      //      }
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

  override def finalCheck: Boolean = {
    assertAllRemaining
    true
  }

  /* Transformations */

  def treeToZ3(tree: Tree): Z3AST = treeToZ3_rec(purify(z3, tree))

  private def treeToZ3_rec(tree: Tree): Z3AST = tree match {
    case Var(sym) => sym.ast
    case Lit(TrueLit) => z3.mkTrue
    case Lit(FalseLit) => z3.mkFalse
    case Lit(IntLit(i)) => z3.mkInt(i, z3.mkIntSort)
    case Op(AND, ts) => z3.mkAnd((ts map treeToZ3_rec): _*)
    case Op(OR, ts) => z3.mkOr((ts map treeToZ3_rec): _*)
    case Op(NOT, Seq(t)) => z3.mkNot(treeToZ3_rec(t))
    case Op(IFF, Seq(t1, t2)) => z3.mkIff(treeToZ3_rec(t1), treeToZ3_rec(t2))
    //    case Op(EQ, Seq(Op(CARD, Seq(t)), Lit(IntLit(1)))) => mkIsSingleton(treeToZ3_rec(t))
    //    case Op(EQ, Seq(Lit(IntLit(1)), Op(CARD, Seq(t)))) => mkIsSingleton(treeToZ3_rec(t))
    case Op(EQ, Seq(t1, t2)) => z3.mkEq(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(LT, Seq(t1, t2)) => z3.mkLT(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(ADD, ts) => z3.mkAdd((ts map treeToZ3_rec): _*)
    case Op(CARD, Seq(t)) => mkCard(treeToZ3_rec(t))
    case Op(SETEQ, Seq(t1, t2)) => z3.mkEq(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(SUBSETEQ, Seq(t1, t2)) => mkSubsetEq(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(UNION, ts) => mkUnion((ts map treeToZ3_rec): _*)
    case Op(INTER, ts) => mkIntersect((ts map treeToZ3_rec): _*)
    case Op(COMPL, Seq(t)) => mkComplement(treeToZ3_rec(t))
    case Lit(EmptySetLit) => mkEmptySet
    case _ => error("Unsupported conversion from BAPA-tree to Z3AST :\n" + tree)
  }

  def knownRepresentative(ast: Z3AST): Z3AST = ast

  def z3ToTree(ast: Z3AST): Tree = z3.getASTKind(ast) match {
    case _ if ast == mkEmptySet => EmptySet
    case Z3AppAST(decl, Nil) => SetSymbol(knownRepresentative(ast))
    case Z3AppAST(decl, args) if decl == mkSubsetEq => Op(SUBSETEQ, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkUnion => Op(UNION, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkIntersect => Op(INTER, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkComplement => Op(COMPL, args map z3ToTree)
    //    case Z3AppAST(decl, args) if decl == mkIsSingleton => z3ToTree(args(0)).card === 1
    //    case Z3AppAST(decl, args) if decl == mkCardPred => Op(EQ, Seq(Op(CARD, Seq(z3ToTree(args(0)))), IntSymbol(args(1))))
    case Z3AppAST(decl, args) if decl == mkCard => Op(CARD, Seq(z3ToTree(args(0))))
    case _ =>
      //println("** Cannot convert Z3AST to BAPA-tree :\n** " + ast)
      //println("** Treating it as an uninterpreted function")
      SetSymbol(knownRepresentative(ast))
  //       println("** Cannot convert Z3AST to BAPA tree :\n** " + ast)
  //       error("Cannot convert Z3AST to BAPA tree")
  }

  def NaiveBapaToPaTranslator(tree0: Tree) = {
    def rec(tree: Tree): Tree = tree match {
      case Op(CARD, Seq(set)) => universeStack.head translate set
      case Op(op, ts) => Op(op, ts map rec)
      case Var(_) | Lit(_) => tree
    }
    val tree1 = simplify(tree0)
    universeStack.push(universeStack.pop addSets setVariables(tree1))
    simplify(rec(simplify(rewriteSetRel(tree1))))
  }

}
