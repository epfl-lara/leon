package z3.scala

import z3.Pointer
import z3.Z3Wrapper

/** This class is inherited to create user defined theories.
 * <p>
 * The class should
 * be instantiated before anything is added to the <code>Z3Context</code>, as
 * constructing the class automatically registers the plugin with the context.
 * The user can choose which callbacks to activate by calling
 * <code>setCallbacks</code> with the appropriate arguments at construction
 * time. For debugging purposes, the method <code>showCallbacks</code> can be
 * useful. */
abstract class Z3Theory(context: Z3Context, val name: String) {
  // This will immediately set the pointer.
  val ptr : Long = Z3Wrapper.mkTheory(context.ptr, name)
  private val proxy = new TheoryProxy(context, this)

  /** Use this function at construction time to set which callbacks should be used. */
  final def setCallbacks(
    delete: Boolean = false,
    reduceEq: Boolean = false,
    reduceApp: Boolean = false,
    reduceDistinct: Boolean = false,
    newApp: Boolean = false,
    newElem: Boolean = false,
    initSearch: Boolean = false,
    push: Boolean = false,
    pop: Boolean = false,
    restart: Boolean = false,
    reset: Boolean = false,
    finalCheck: Boolean = false,
    newEq: Boolean = false,
    newDiseq: Boolean = false,
    newAssignment: Boolean = false,
    newRelevant: Boolean = false) : Unit = {
    Z3Wrapper.setTheoryCallbacks(this.ptr, proxy, delete, reduceEq, reduceApp, reduceDistinct, newApp, newElem, initSearch, push, pop, restart, reset, finalCheck, newEq, newDiseq, newAssignment, newRelevant)
  } 

  /** Displays all callbacks, with their arguments. Off by default.
    * @param show whether callbacks should be printed out */
  final def showCallbacks(show: Boolean) : Unit = proxy.showCalls(true, name)

  private def noImplWarning(mn: String) : Unit = {
    System.err.println("Warning: '" + mn + "' was called back but is not implemented.")
  }

  // The functions in the following block are the callbacks.

  /** Method that Z3 will call (if activated) to delete the theory. After that
   * call, no more callbacks will be made by Z3. */
  def delete : Unit = {
    noImplWarning("delete")
  }

  /** Method that Z3 will call (if activated) to simplify an equality tree,
   * when the operands are of a theory sort. 
   * @param term1 the left operand of the equality 
   * @param term2 the right operand of the equality */
  def reduceEq(term1: Z3AST, term2: Z3AST) : Option[Z3AST] = {
    noImplWarning("reduceEq")
    None
  }

  /** Method that Z3 will call (if activated) to simplify an application of a
   * theory function. */
  def reduceApp(funcDecl: Z3FuncDecl, args: Z3AST*) : Option[Z3AST] = {
    noImplWarning("reduceApp")
    None
  }

  /** Method that Z3 will call (if activated) to simplify a (n-ary) disequality
   * tree, when the operands are of a theory sort. */
  def reduceDistinct(terms: Z3AST*) : Option[Z3AST] = {
    noImplWarning("reduceDistinct")
    None
  }

  /** Method that Z3 will call (if activated) when an application of a theory
   * function enters the context. */
  def newApp(app: Z3AST) : Unit = {
    noImplWarning("newApp")
  }

  /** Method that Z3 will call (if activated) when an element of a theory sort
   * enters the context. */
  def newElem(elem: Z3AST) : Unit = {
    noImplWarning("newElem")
  }

  /** Method that Z3 will call (if activated) when it starts the search. */
  def initSearch : Unit = {
    noImplWarning("initSearch")
  }

  /** Method that Z3 will call (if activated) when it creates a case-split
   * (backtracking point). */
  def push : Unit = {
    noImplWarning("push")
  }

  /** Method that Z3 will call (if activated) when it backtracks a case-split. */
  def pop : Unit = {
    noImplWarning("pop")
  }

  /** Method that Z3 will call (if activated) when it restarts the search. */
  def restart : Unit = {
    noImplWarning("restart")
  }

  /** Method that Z3 will call (if activated) when the context is reset by the
   * user. */
  def reset : Unit = {
    noImplWarning("reset")
  }

  /** Method that Z3 will call (if activated) just before Z3 starts building a
   * model. */
  def finalCheck : Boolean = {
    noImplWarning("finalCheck")
    true
  }

  /** Method that Z3 will call (if activated) when an equality is concluded in
   * the logical context. */
  def newEq(term1: Z3AST, term2: Z3AST) : Unit = {
    noImplWarning("newEq")
  }

  /** Method that Z3 will call (if activated) when a disequality is concluded
   * in the logical context. */
  def newDiseq(term1: Z3AST, term2: Z3AST) : Unit = {
    noImplWarning("newDiseq")
  }

  /** Method that Z3 will call (if activated) when a theory predicate is
   * assigned to a truth value in the logical context. 
   * @param pred the predicate
   * @param polarity its truth value in the context */
  def newAssignment(pred: Z3AST, polarity: Boolean) : Unit = {
    noImplWarning("newAssignment")
  }

  def newRelevant(ast: Z3AST) : Unit = {
    noImplWarning("newRelevant")
  }

  // The following is to be used at initialization time.
  final def mkTheorySort(symbol: Z3Symbol) : Z3Sort = new Z3Sort(Z3Wrapper.theoryMkSort(context.ptr, this.ptr, symbol.ptr), context)
  final def mkTheoryValue(symbol: Z3Symbol, sort: Z3Sort) : Z3AST = new Z3AST(Z3Wrapper.theoryMkValue(context.ptr, this.ptr, symbol.ptr, sort.ptr), context)
  final def mkTheoryConstant(symbol: Z3Symbol, sort: Z3Sort) : Z3AST = new Z3AST(Z3Wrapper.theoryMkConstant(context.ptr, this.ptr, symbol.ptr, sort.ptr), context)
  final def mkTheoryFuncDecl(symbol: Z3Symbol, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = new Z3FuncDecl(Z3Wrapper.theoryMkFuncDecl(context.ptr, this.ptr, symbol.ptr, domainSorts.size, toPtrArray(domainSorts), rangeSort.ptr), domainSorts.size, context)

  // These functions enable the communication with the DPLL+UF engine.
  final def getContext : Z3Context = context

  /** Adds an axiom to the logical context. The axiom should always be a
   * tautology with respect to the theory. The axiom is guaranteed to be
   * maintained in all (backtracking) levels beyond the one where it is
   * asserted. Note that in the current version, calling
   * <code>assertAxiom</code> from within the following callbacks does not
   * work: <code>newElem</code>, <code>newApp</code>, <code>push</code>,
   * <code>pop</code>. It is <i>strongly</i> advised to call it from within the
   * following callbacks only: </code>newEq</code>, <code>newDiseq</code>,
   * <code>newAssignment</code>, <code>finalCheck</code>. It is unclear whether
   * this is a bug with Z3 or a feature. */
  final def assertAxiom(axiom: Z3AST) : Unit = Z3Wrapper.theoryAssertAxiom(this.ptr, axiom.ptr)

  /** Indicates to Z3 that in the model being built by the theory, two elements are equal. */
  final def assumeEq(lhs: Z3AST, rhs: Z3AST) : Unit = Z3Wrapper.theoryAssumeEq(this.ptr, lhs.ptr, rhs.ptr)

  final def enableAxiomSimplification(flag: Boolean) : Unit = Z3Wrapper.theoryEnableAxiomSimplification(this.ptr, flag)
  final def getEqClassRoot(ast: Z3AST) : Z3AST = new Z3AST(Z3Wrapper.theoryGetEqCRoot(this.ptr, ast.ptr), context)
  final def getEqClassNext(ast: Z3AST) : Z3AST = new Z3AST(Z3Wrapper.theoryGetEqCNext(this.ptr, ast.ptr), context)

  /** Returns an iterator over all elements of the equivalence class of a term. */
  final def getEqClassMembers(ast: Z3AST) : Iterator[Z3AST] = {
    val theory = this
    new Iterator[Z3AST] {
      val root: Long = Z3Wrapper.theoryGetEqCRoot(theory.ptr, ast.ptr)
      var nxt: Long = Z3Wrapper.theoryGetEqCNext(theory.ptr, root)
      var calledOnce = false

      override def hasNext : Boolean = (!calledOnce || nxt != root)
      override def next() : Z3AST = {
        if(!calledOnce) {
          calledOnce = true
          new Z3AST(root, context)
        } else {
          val toReturn = new Z3AST(nxt, context)
          nxt = Z3Wrapper.theoryGetEqCNext(theory.ptr, nxt)
          toReturn
        }
      }
    }
  }

  final def getNumParents(ast: Z3AST) : Int = Z3Wrapper.theoryGetNumParents(this.ptr, ast.ptr)
  final def getParent(ast: Z3AST, i: Int) : Z3AST = new Z3AST(Z3Wrapper.theoryGetParent(this.ptr, ast.ptr, i), context)

  /** Returns an iterator over all terms that have a given term as a subtree. */
  final def getParents(ast: Z3AST) : Iterator[Z3AST] = {
    val theory = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.theoryGetNumParents(theory.ptr, ast.ptr)
      var returned : Int = 0
      
      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.theoryGetParent(theory.ptr, ast.ptr, returned), context)
        returned += 1
        toReturn
      }
    }
  }

  final def isTheoryValue(v: Z3AST) : Boolean = Z3Wrapper.theoryIsValue(this.ptr, v.ptr)
  final def isTheoryDecl(f: Z3FuncDecl) : Boolean = Z3Wrapper.theoryIsDecl(this.ptr, f.ptr)

  final def getNumElems : Int = Z3Wrapper.theoryGetNumElems(this.ptr)
  final def getElem(i: Int) : Z3AST = new Z3AST(Z3Wrapper.theoryGetElem(this.ptr, i), context)

  /** Returns an iterator over all theory elements in the context. */
  final def getElems : Iterator[Z3AST] = {
    val theory = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.theoryGetNumElems(theory.ptr)
      var returned : Int = 0
      
      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.theoryGetElem(theory.ptr, returned), context)
        returned += 1
        toReturn
      }
    }
  }

  final def getNumApps : Int = Z3Wrapper.theoryGetNumApps(this.ptr)
  final def getApp(i: Int) : Z3AST = new Z3AST(Z3Wrapper.theoryGetApp(this.ptr, i), context)

  /** Returns an iterator over all theory function applications in the context. */
  final def getApps : Iterator[Z3AST] = {
    val theory = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.theoryGetNumApps(theory.ptr)
      var returned : Int = 0
      
      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.theoryGetApp(theory.ptr, returned), context)
        returned += 1
        toReturn
      }
    }
  }
}
