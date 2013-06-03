/* Copyright 2009-2013 EPFL, Lausanne */

/********************************************************************

   WARNING : THIS VERSION IS NOT USED (AND CERTAINLY NOT MAINTAINED).
   SEE BAPATheoryBubbles INSTEAD !

   ******************************************************************/

package purescala.z3plugins.bapa

import scala.collection.mutable.{Stack, ArrayBuffer, Set => MutableSet, Map => MutableMap}
import scala.collection.immutable.{Map => ImmutableMap}
import z3.scala._
import AST._
import NormalForms.{simplify, setVariables, rewriteSetRel}

import scala.sys.error

class BAPATheoryEqc(val z3: Z3Context) extends Z3Theory(z3, "BAPATheory (eqc)") with VennRegions {

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

  private var universe: Universe = null
  private val clauseStack = new Stack[Stack[Seq[Clause]]]
  //   private val boundaryElemsStack = new Stack[Set[Z3AST]]
  //   boundaryElemsStack push Set.empty[Z3AST]

  private sealed abstract class Clause
  private case class CardClause(tree: Tree) extends Clause
  private case class SingletonClause(tree: Tree) extends Clause
  private case class AssignClause(tree: Tree, polarity: Boolean) extends Clause
  private case class EqClause(tree1: Tree, tree2: Tree) extends Clause
  private case class DiseqClause(tree1: Tree, tree2: Tree) extends Clause

  private def addClause(clause: Clause) {
    //     println("  Clause: " + clause)
    //     clauseStack.head.head += clause

    // Try to assert clause axiom immediately, push it otherwise
    transformClause(clause) match {
      case (newClause, newSymbols) if newSymbols.isEmpty =>
        print(". ")
        assertClause(newClause)
      case (_, newSymbols) =>
        print(newSymbols.size + " ")
        clauseStack.head push (clause +: clauseStack.head.pop)
    }
  }

  def showStack = {
    (clauseStack map {cls => (cls map {cl => cl.size}).mkString("{", ",", "}")}).mkString("{", ",", "}")
  }

  /* Axiom assertion helper functions */

  def assertAxiomSafe(axiom: Z3AST) {
    if (canAssertAxiom) {
      assertAxiom(axiom)
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
          assertAxiom(ax)
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
    universe = new EmptyUniverse(mkDomainSize)
    clauseStack.clear
    clauseStack push new Stack[Seq[Clause]]
    axiomsToAssert.clear
    pushLevel = 0
    push
  }
  init

  override def reset {
    init
    //     new AssertionError("Reset was called").printStackTrace
  }

  override def restart {
    init
    //     new AssertionError("Restart was called").printStackTrace
  }

  override def push {
    pushLevel += 1
    clauseStack.head push Seq[Clause]()
    //     println("Push level " + pushLevel + "   " + showStack)
  }

  override def pop {
    //     println("Pop  level " + pushLevel + "   " + showStack)
    pushLevel -= 1
    clauseStack.head.pop
    while (clauseStack.head.isEmpty) {
      clauseStack.pop
      clauseStack.head.pop
    }

    //     println("---------- " + pushLevel + "   " + showStack)
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

  override def newAssignment(ast: Z3AST, polarity: Boolean) = safeBlockToAssertAxioms {
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
    ()
  }

  override def newEq(ast1: Z3AST, ast2: Z3AST) = safeBlockToAssertAxioms {

    if (z3.getSort(ast1) == mkSetSort) {
      /*
      inclusionStack.push(inclusionStack.pop.newEq(ast1, ast2))
      */
      //       println("Equals : " + (ast1 == ast2))
      //       println("Root Equals : " + (getEqClassRoot(ast1) == getEqClassRoot(ast2)))
      //       println("Ast 1 : " + ast1)
      //       println("Ast 2 : " + ast2)
      //       println("Ast 1 root : " + getEqClassRoot(ast1))
      //       println("Ast 2 root : " + getEqClassRoot(ast2))
      //       println("Ast 1 class : " + getEqClassMembers(ast1).toList.mkString(", "))
      //       println("Ast 2 class : " + getEqClassMembers(ast2).toList.mkString(", "))
      //       println("Ast 1 parents : " + getParents(ast1).toList.mkString(", "))
      //       println("Ast 2 parents : " + getParents(ast2).toList.mkString(", "))

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
    ()
  }

  override def newDiseq(ast1: Z3AST, ast2: Z3AST) = safeBlockToAssertAxioms {

    if (z3.getSort(ast1) == mkSetSort) {
      //       println("*** new Diseq : " + ast1 + "  ==  " + ast2)
      //       println("Ast 1 : " + ast1)
      //       println("Ast 2 : " + ast2)
      //       println("Ast 1 root : " + getEqClassRoot(ast1))
      //       println("Ast 2 root : " + getEqClassRoot(ast2))
      //       println("Ast 1 class : " + getEqClassMembers(ast1).toList.mkString(", "))
      //       println("Ast 2 class : " + getEqClassMembers(ast2).toList.mkString(", "))
      //       println("Ast 1 parents : " + getParents(ast1).toList.mkString(", "))
      //       println("Ast 2 parents : " + getParents(ast2).toList.mkString(", "))

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
    ()
  }

  private def assertClause(clause: Clause) = clause match {
    case CardClause(bapaTree) =>
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkEq(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
    case SingletonClause(tree) =>
    // nothing to do (except optimizations :P)
    case AssignClause(tree, polarity) =>
      val bapaTree = if (polarity) tree else !tree
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
    case EqClause(tree1, tree2) =>
      val bapaTree = tree1 seteq tree2
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
    case DiseqClause(tree1, tree2) =>
      val bapaTree = !(tree1 seteq tree2)
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
  }

  override def finalCheck: Boolean = safeBlockToAssertAxioms {
    println("\n==== Final check ====")

    val clauses = clauseStack.head flatMap {cl => cl}
    val boundary = getBoundaryElems

    clauseStack push new Stack[Seq[Clause]]
    clauseStack.head push Seq[Clause]()

    // Prints all clauses at final check
    /*
    println("Clauses\n")
    for (cl <- clauses) cl match {
      case CardClause(ast) =>
        println(z3ToTreeEqc(ast))
      case SingletonClause(ast) =>
        // nothing to do (except optimizations :P)
      case AssignClause(ast, polarity) =>
        val bapaTree = if (polarity) z3ToTreeEqc(ast) else !z3ToTreeEqc(ast)
        println(bapaTree)
      case EqClause(ast1, ast2) =>
        val bapaTree = z3ToTreeEqc(ast1) seteq z3ToTreeEqc(ast2)
        println(bapaTree)
      case DiseqClause(ast1, ast2) =>
        val bapaTree = !(z3ToTreeEqc(ast1) seteq z3ToTreeEqc(ast2))
        println(bapaTree)
    }
//     error("STOP")
    */

    val ((newClauses, newBoundary), newSymbols) = transformClausesAndBoundary(clauses, boundary)

    // Extend universe
    universe = universe addSets newSymbols

    println
    println("===> Number of set variables at final check :  " + universe.setVariables.size
            + " (just added " + newSymbols.size + ")")
    println

    // Assert axioms for clauses
    newClauses foreach assertClause

    // Axioms for venn regions
    universe.assertAllAxioms

    // Axioms for implied set equalities
    val B = newBoundary.toArray
    for (i <- 0 until B.size; j <- 0 until i) {
      val bapaTree = B(i) seteq B(j)
      val paTree = NaiveBapaToPaTranslator(B(i) seteq B(j))
      assertAxiomSafe(z3.mkIff(
        treeToZ3(bapaTree),
        treeToZ3(paTree)
        ))
    }

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
    case Op(UNION, ts) => ts map treeToZ3 reduceLeft {(t1, t2) => mkUnion(t1, t2)}
    case Op(INTER, ts) => ts map treeToZ3 reduceLeft {(t1, t2) => mkIntersect(t1, t2)}
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
      case Z3AppAST(decl, args) if decl == mkCard => Op(CARD, args map z3ToTree)
      case _ => SetSymbol(ast)
    }
  }

  private def mapClause(f: Tree => Tree)(clause: Clause): Clause = clause match {
    case CardClause(tree) => CardClause(f(tree))
    case SingletonClause(tree) => SingletonClause(f(tree))
    case AssignClause(tree, polarity) => AssignClause(f(tree), polarity)
    case EqClause(tree1, tree2) => EqClause(f(tree1), f(tree2))
    case DiseqClause(tree1, tree2) => DiseqClause(f(tree1), f(tree2))
  }

  private def transformClausesAndBoundary(clauses: Seq[Clause], boundary: Seq[Tree]): ((Seq[Clause], Seq[Tree]), Seq[Symbol]) = {
    def accept(f: Tree => Tree): (Seq[Clause], Seq[Tree]) = {
      val newClauses = clauses map mapClause(f)
      val newBoundary = boundary map f
      (newClauses, newBoundary)
    }
    eqcTransform(accept)
  }

  private def transformClause(clause: Clause): (Clause, Seq[Symbol]) = {
    eqcTransform(f => mapClause(f)(clause))
  }

  // Returns transformed clauses (after eqc lookup) and new symbols to add
  def eqcTransform[A](callback: (Tree => Tree) => A): (A, Seq[Symbol]) = {
    var symbolsBeingAdded = new ArrayBuffer[Symbol]
    def canonicalize2(tree: Tree): Tree = canonicalize(simplify(tree))
    def canonicalize(tree: Tree): Tree = tree match {
      case Var(symbol) => knownRepresentative(symbol)
      case Op(op, args) => Op(op, args map canonicalize)
      case Lit(_) => tree
    }
    //     def canonicalize2(tree: Tree) = canonicalize(simplify(tree))
    //     def canonicalize(clause: Clause): Clause = clause match {
    //       case CardClause(tree) => CardClause(canonicalize2(tree))
    //       case SingletonClause(tree) => SingletonClause(canonicalize2(tree))
    //       case AssignClause(tree1, tree2) => AssignClause(canonicalize2(tree1), canonicalize2(tree2))
    //       case EqClause(tree1, tree2) => AssignClause(canonicalize2(tree1), canonicalize2(tree2))
    //       case DiseqClause(tree1, tree2) => AssignClause(canonicalize2(tree1), canonicalize2(tree2))
    //     }
    def knownRepresentative(symbol: Symbol): Tree = {
      if (getEqClassMembers(symbol.ast) contains mkEmptySet) {
        //       println("KNOWN REPRESENTATIVE :  " + symbol + "  ->  " + EmptySet)
        return EmptySet
      }
      val knownSymbols = universe.variables ++ symbolsBeingAdded
      if (!(knownSymbols contains symbol)) {
        for (congruent <- getEqClassMembers(symbol.ast)) {
          val tree = z3ToTree(congruent)
          if (setVariables(tree) forall knownSymbols.contains) {
            //           println("KNOWN REPRESENTATIVE :  " + symbol + "  ->  " + tree)
            return tree
          }
        }
        // extend universe
        symbolsBeingAdded += symbol
        //       universe += symbol
      }
      symbol
    }
    val result = callback(canonicalize2)
    //     val newClauses = clauses map canonicalize
    (result, symbolsBeingAdded.toSeq)
  }

  //   private val interpretedFunctions = Seq(mkCard, mkSubsetEq, mkUnion, mkIntersect, mkComplement)

  def getBoundaryElems = {
    // 'Smart' search that checks parents [BROKEN]
    /*
    for (elem <- getElems; if z3.getSort(elem) == mkSetSort; parent <- getParents(elem)) z3.getASTKind(parent) match {
      case Z3AppAST(decl, args) =>
        if ((args contains elem) && (interpretedFunctions contains decl)) {
          boundary += z3ToTreeEqc(elem)
        }
      case _ =>
    }
    for (app <- getApps; if z3.getSort(app) == mkSetSort; parent <- getParents(app)) z3.getASTKind(parent) match {
      case Z3AppAST(decl, args) =>
        if ((args contains app) && (interpretedFunctions contains decl)) {
          boundary += z3ToTreeEqc(app)
        }
      case _ =>
    }
    */

    val boundary = MutableSet[Tree]()
    for (elem <- getElems; if z3.getSort(elem) == mkSetSort)
      boundary += z3ToTree(elem)
    for (app <- getApps; if z3.getSort(app) == mkSetSort)
      boundary += z3ToTree(app)
    boundary.toSeq
  }

  def NaiveBapaToPaTranslator(tree0: Tree) = {
    def rec(tree: Tree): Tree = tree match {
      case Op(CARD, Seq(set)) => universe translate set
      case Op(op, ts) => Op(op, ts map rec)
      case Var(_) | Lit(_) => tree
    }
    val tree1 = simplify(tree0)
    if (setVariables(tree1) exists {x => !(universe.variables contains x)}) {
      error("No new venn regions should be created at this point")
    }
    //     universe = universe addSets setVariables(tree1)
    simplify(rec(simplify(rewriteSetRel(tree1))))
  }
}
