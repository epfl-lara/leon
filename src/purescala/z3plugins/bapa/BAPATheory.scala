package purescala.z3plugins.bapa

// import scala.collection.mutable.{Stack,ArrayBuffer,HashSet,HashMap}
import scala.collection.mutable.Stack
import scala.collection.mutable.{Set => MutableSet}
import scala.collection.immutable.{Map => ImmutableMap}
import z3.scala._
import AST._
import NormalForms.{simplify, rewriteSetRel, setVariables, purify}

class BAPATheory(val z3: Z3Context) extends Z3Theory(z3, "BAPATheory") with VennRegions {
  // def this() = this(new Z3Context(new Z3Config("MODEL" -> true)))
  //def this() = this(new Z3Context(new Z3Config("MODEL" -> true, "RELEVANCY" -> 0)))
  setCallbacks(
//     initSearch = true,
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

// This makes the Theory Proxy print out all calls that are forwarded to the theory.
  //showCallbacks(true)

  /* Theory constructs */
  
  val mkSetSort = mkTheorySort(z3.mkStringSymbol("SetSort"))
  val mkEmptySet = mkTheoryValue(z3.mkStringSymbol("EmptySet"), mkSetSort)
  val mkIsSingleton = mkUnarySetfun("IsSingleton", z3.mkBoolSort)
  val mkCard = mkUnarySetfun("Cardinality", z3.mkIntSort)
  val mkCardPred = mkTheoryFuncDecl(z3.mkStringSymbol("HasCardinality"), Seq(mkSetSort, z3.mkIntSort), z3.mkBoolSort)
  val mkElementOf = mkTheoryFuncDecl(z3.mkStringSymbol("IsElementOf"), Seq(z3.mkIntSort, mkSetSort), z3.mkBoolSort)
  val mkAsSingleton = mkTheoryFuncDecl(z3.mkStringSymbol("AsSingleton"), Seq(z3.mkIntSort), mkSetSort)
  val mkAsElement = mkUnarySetfun("AsElement", z3.mkIntSort)
  val mkSubsetEq = mkBinarySetfun("SubsetEq", z3.mkBoolSort)
  val mkUnion = mkBinarySetfun("Union", mkSetSort)
  val mkIntersect = mkBinarySetfun("Intersect", mkSetSort)
  val mkComplement = mkUnarySetfun("Complement", mkSetSort)
  val mkDomainSize = z3.mkFreshConst("DomainSize", z3.mkIntSort)

  def mkDisjoint(set1: Z3AST, set2: Z3AST) =
    z3.mkEq(mkIntersect(set1, set2), mkEmptySet)

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
  
  private val stack = new Stack[Universe]
  stack push new EmptyUniverse(mkDomainSize)

  /* Callbacks */

//   override def assertAxiom(ast: Z3AST) {
//     println(ast)
//     assertAxiom(ast)
//   }

  // We use this trick to circumvent the fact that you (apparently) can't
  // assertAxioms with some callbacks, such as newApp...
  private val axiomsToAssert: MutableSet[Z3AST] = MutableSet.empty
  private def assertAxiomEventually(axiom: Z3AST) = {
    axiomsToAssert += axiom
  }
  private def assertAllRemaining : Unit = {
    if(axiomsToAssert.nonEmpty) {
      for(ax <- axiomsToAssert) {
        println("Asserting eventual axiom: " + ax)
        assertAxiom(ax)
      }
      axiomsToAssert.clear
    }
  }

  override def reset {
    knownSetExprs = Nil
    axiomsToAssert.clear
    stack.clear
  }

  override def restart {
    knownSetExprs = Nil
    axiomsToAssert.clear
    stack.clear
  }

  override def push { stack push stack.head }

  override def pop { stack.pop }

  override def newAssignment(ast: Z3AST, polarity: Boolean) {
    assertAllRemaining
//     println("*** new App : " + ast + " is set to " + polarity)
    val assumption = if (polarity) ast else z3.mkNot(ast)
    val bapaTree = if (polarity) z3ToTree(ast) else !z3ToTree(ast)
    val paTree = NaiveBapaToPaTranslator(bapaTree)
    val axiom = z3.mkImplies(assumption, treeToZ3(paTree))
    assertAxiom(axiom)
//     println(axiom)
//     println("New Axiom       : " + bapaTree + " implies\n" + paTree)
  }

  override def newEq(ast1: Z3AST, ast2: Z3AST) {
    assertAllRemaining

    if(z3.getSort(ast1) == mkSetSort) {
      // TODO: if either ast1 or ast2 is a variable => don't add it/remove it from the stack and remember congruence class
//       println("*** new Eq : " + ast1 + "  ==  " + ast2)

      /*
      println("Equals : " + (ast1 == ast2))
      println("Root Equals : " + (getEqClassRoot(ast1) == getEqClassRoot(ast2)))
      println("Ast 1 : " + ast1)
      println("Ast 2 : " + ast2)
      println("Ast 1 root : " + getEqClassRoot(ast1))
      println("Ast 2 root : " + getEqClassRoot(ast2))
      */
      
      val assumption = z3.mkEq(ast1, ast2)
      val bapaTree = z3ToTree(ast1) seteq z3ToTree(ast2)
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      val axiom = z3.mkImplies(assumption, treeToZ3(paTree))
      assertAxiom(axiom)
    }
  }

  override def newDiseq(ast1: Z3AST, ast2: Z3AST) {
    assertAllRemaining
//     println("*** new Diseq : " + ast1 + "  ==  " + ast2)
    
    if(z3.getSort(ast1) == mkSetSort) {
      val assumption = z3.mkDistinct(ast1, ast2)
      val bapaTree = !(z3ToTree(ast1) seteq z3ToTree(ast2))
      val paTree = NaiveBapaToPaTranslator(bapaTree)
      val axiom = z3.mkImplies(assumption, treeToZ3(paTree))
      assertAxiom(axiom)
    }
  }

  override def newApp(ast: Z3AST) {
//    println("*** new App : " + ast)
    z3.getASTKind(ast) match {
      case Z3AppAST(decl, args) if decl == mkCard =>
        val bapaTree = z3ToTree(ast) === Var(IntSymbol(ast))
        val paTree = NaiveBapaToPaTranslator(bapaTree)
        val axiom = treeToZ3(paTree)
        assertAxiomEventually(axiom)
//        println(axiom)
//        println("New (eventual) Axiom     : " + paTree)
      case _ =>
     // ignore other functions
    }
  }

  override def initSearch : Unit = {
    // Indicates that mkUnion is commutative
    // val b1 = z3.mkBound(0, mkSetSort)
    // val b2 = z3.mkBound(1, mkSetSort)
    // val pattern = z3.mkPattern(mkUnion(b1, b2))
    // val axiomTree = z3.mkEq(mkUnion(b1,b2),mkUnion(b2,b1))
    // // TODO: make sure these symbols are unique.
    // val bn1 = z3.mkIntSymbol(0)
    // val bn2 = z3.mkIntSymbol(1)
    // val axiom = z3.mkForAll(0, List(pattern), List((bn1, mkSetSort), (bn2, mkSetSort)), axiomTree)
    // z3.assertCnstr(axiom)
  }

  // TODO: add reductions for union & inter (empty set) and compl (nnf ?)
  override def reduceApp(fd: Z3FuncDecl, args: Z3AST*) : Option[Z3AST] = {
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
    } else if (fd == mkIsSingleton) {
      if (args(0) == mkEmptySet) {
        Some(z3.mkFalse)
      } else {
        None
      }
    } else if (fd == mkElementOf) {
      val elem = args(0)
      val set  = args(1)
      if (set == mkEmptySet) {
        Some(z3.mkFalse)
      } else {
        val singleton = z3.mkFreshConst("singleton", mkSetSort)
        Some(z3.mkAnd(
          mkIsSingleton(singleton),
          z3.mkEq(mkAsSingleton(elem), singleton),
          z3.mkEq(mkAsElement(singleton), elem),
          mkSubsetEq(singleton, set)
        ))
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
    case Op(AND, ts) => z3.mkAnd((ts map treeToZ3_rec):_*)
    case Op(OR, ts) => z3.mkOr((ts map treeToZ3_rec):_*)
    case Op(NOT, Seq(t)) => z3.mkNot(treeToZ3_rec(t))
    case Op(IFF, Seq(t1, t2)) => z3.mkIff(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(EQ, Seq(Op(CARD, Seq(t)), Lit(IntLit(1)))) => mkIsSingleton(treeToZ3_rec(t))
    case Op(EQ, Seq(Lit(IntLit(1)), Op(CARD, Seq(t)))) => mkIsSingleton(treeToZ3_rec(t))
    case Op(EQ, Seq(t1, t2)) => z3.mkEq(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(LT, Seq(t1, t2)) => z3.mkLT(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(ADD, ts) => z3.mkAdd((ts map treeToZ3_rec):_*)
    case Op(ITE, Seq(t1, t2, t3)) => z3.mkITE(treeToZ3_rec(t1), treeToZ3_rec(t2), treeToZ3_rec(t3))
//     case Op(CARD, Seq(t)) => mkCard(treeToZ3_rec(t))
    case Op(CARD_PRED, Seq(s, t)) => mkCardPred(treeToZ3_rec(s), treeToZ3_rec(t))
    case Op(SETEQ, Seq(t1, t2)) => z3.mkEq(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(SUBSETEQ, Seq(t1, t2)) => mkSubsetEq(treeToZ3_rec(t1), treeToZ3_rec(t2))
    case Op(UNION, ts) => mkUnion((ts map treeToZ3_rec):_*)
    case Op(INTER, ts) => mkIntersect((ts map treeToZ3_rec):_*)
    case Op(COMPL, Seq(t)) => mkComplement(treeToZ3_rec(t))
    case Lit(EmptySetLit) => mkEmptySet
    case _ => error("Unsupported conversion from BAPA-tree to Z3AST :\n" + tree)
  }

  private var knownSetExprs: List[Z3AST] = Nil
  private def knownRepresentative(set: Z3AST) : Z3AST = {
    // This can get slow in theory. I'd use a Set for inClass, but the hashing
    // of Z3AST does not seem to work like it should. We need to check whether
    // we can trust the C pointer to be a valid hash.
    var inClass: List[Z3AST] = Nil

    var current = set
    do {
      inClass = current :: inClass
      current = getEqClassNext(current)
    } while(current != set)
    inClass = inClass.reverse

    // println(" -- Equivalence class contains " + inClass)
    // println(" -- List is " + knownSetExprs)

    val result = knownSetExprs.find(inClass.contains(_)) match {
      case Some(repr) => repr
      case None => {
        knownSetExprs = knownSetExprs ::: List(set)
        set
      }
    }

    // println("  -- Known representative for : " + set + " is : " + result)
    result
  }

  def z3ToTree(ast: Z3AST): Tree = z3.getASTKind(ast) match {
    case _ if ast == mkEmptySet => EmptySet
    case Z3AppAST(decl, Nil) => SetSymbol(knownRepresentative(ast))
    case Z3AppAST(decl, args) if decl == mkSubsetEq => Op(SUBSETEQ, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkUnion => Op(UNION, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkIntersect => Op(INTER, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkComplement => Op(COMPL, args map z3ToTree)
    case Z3AppAST(decl, args) if decl == mkIsSingleton => z3ToTree(args(0)).card === 1
    case Z3AppAST(decl, args) if decl == mkCardPred => Op(EQ, Seq(Op(CARD, Seq(z3ToTree(args(0)))), IntSymbol(args(1))))
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
      case Op(CARD, Seq(set)) => stack.head translate set
      case Op(op, ts) => Op(op, ts map rec)
      case Var(_) | Lit(_) => tree
    }
    val tree1 = simplify(tree0)
    stack.push( stack.pop addSets setVariables(tree1))
    simplify(rec(simplify(rewriteSetRel(tree1))))
  }
  
}
