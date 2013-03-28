package z3.scala

import z3.Pointer
import z3.Z3Wrapper

import scala.collection.mutable.{Map=>MutableMap,Set=>MutableSet}
import scala.util.Random.nextInt

class ProceduralAttachment[T](context: Z3Context) extends Z3Theory(context, "PA" + nextInt) {
  private def randomName(prefix: String) : String = prefix + nextInt

  private val thySort : Z3Sort = mkTheorySort(context.mkStringSymbol(randomName("ts-")))
  private val boolSort : Z3Sort = context.mkBoolSort

  private val constants : MutableMap[T,Z3AST] = MutableMap.empty
  private val constantsRev : MutableMap[Z3AST,T] = MutableMap.empty
  def constant(value: T) : Z3AST = constants.get(value) match {
    case Some(v) => v
    case None => {
      val newCst = mkTheoryConstant(context.mkStringSymbol(randomName("tcst-")), thySort)
      constants(value) = newCst
      constantsRev(newCst) = value
      newCst
    }
  }

  def variable : Z3AST = context.mkFreshConst(randomName("var-"), thySort)

  implicit def elemToAST(value : T) : Z3AST = constant(value)
  // implicit def elemToDSLAST(value : T) : dsl.Tree[dsl.BottomSort] = dsl.Z3ASTWrapper[dsl.BottomSort](elemToAST(value))
  implicit def elemToLazyElem(value : T) : (() => T) = {
    (() => value)
  }

  private def boolAST(value : Boolean) : Z3AST = if(value) context.mkTrue else context.mkFalse

  type Pred1 = T => Boolean
  type Pred2 = (T,T) => Boolean
  type Pred3 = (T,T,T) => Boolean
  private val predicates1Rev : MutableMap[Z3FuncDecl,Pred1] = MutableMap.empty
  private val predicates2Rev : MutableMap[Z3FuncDecl,Pred2] = MutableMap.empty
  private val predicates3Rev : MutableMap[Z3FuncDecl,Pred3] = MutableMap.empty
  private val allPredicates : MutableSet[Z3FuncDecl] = MutableSet.empty

  def predicate(pred : Pred1) : Z3FuncDecl = {
    val newPred = mkTheoryFuncDecl(context.mkStringSymbol(randomName("pred1-")), Seq(thySort), boolSort)
    predicates1Rev(newPred) = pred
    allPredicates += newPred
    newPred
  }

  def predicate(pred : Pred2) : Z3FuncDecl = {
    val newPred = mkTheoryFuncDecl(context.mkStringSymbol(randomName("pred2-")), Seq(thySort,thySort), boolSort)
    predicates2Rev(newPred) = pred
    allPredicates += newPred
    newPred
  }

  def predicate(pred : Pred3) : Z3FuncDecl = {
    val newPred = mkTheoryFuncDecl(context.mkStringSymbol(randomName("pred3-")), Seq(thySort,thySort,thySort), boolSort)
    predicates3Rev(newPred) = pred
    allPredicates += newPred
    newPred
  }

  type Fun1 = T => T
  type Fun2 = (T,T) => T
  type Fun3 = (T,T,T) => T
  private val functions1Rev : MutableMap[Z3FuncDecl,Fun1] = MutableMap.empty
  private val functions2Rev : MutableMap[Z3FuncDecl,Fun2] = MutableMap.empty
  private val functions3Rev : MutableMap[Z3FuncDecl,Fun3] = MutableMap.empty
  private val allFunctions : MutableSet[Z3FuncDecl] = MutableSet.empty

  def function(fun : Fun1) : Z3FuncDecl = {
    val newFun = mkTheoryFuncDecl(context.mkStringSymbol(randomName("fun1-")), Seq(thySort), thySort)
    functions1Rev(newFun) = fun
    allFunctions += newFun
    newFun
  }

  def function(fun : Fun2) : Z3FuncDecl = {
    val newFun = mkTheoryFuncDecl(context.mkStringSymbol(randomName("fun2-")), Seq(thySort,thySort), thySort)
    functions2Rev(newFun) = fun
    allFunctions += newFun
    newFun
  }

  def function(fun : Fun3) : Z3FuncDecl = {
    val newFun = mkTheoryFuncDecl(context.mkStringSymbol(randomName("fun3-")), Seq(thySort,thySort,thySort), thySort)
    functions3Rev(newFun) = fun
    allFunctions += newFun
    newFun
  }

  // type PartFun2 = (=>T,=>T) => (()=>T)
  // def partialFunction(funs : PartFun2*) : Z3FuncDecl = {
  //   null
  // }

  private def interpret(fd : Z3FuncDecl, args : Z3AST*) : Option[Z3AST] = {
    assert(args.size != 0)
    if(args.forall(isTheoryConstant(_))) {
      val asElems : Seq[T] = args.map(a => constantsRev(a))
    
      if(predicates1Rev.isDefinedAt(fd)) {
        assert(args.size == 1)
        val f = predicates1Rev(fd)
        Some(boolAST(f(asElems(0))))
      } else if(functions1Rev.isDefinedAt(fd)) {
        assert(args.size == 1)
        val f = functions1Rev(fd)
        Some(constant(f(asElems(0))))      
      } else if(predicates2Rev.isDefinedAt(fd)) {
        assert(args.size == 2)
        val f = predicates2Rev(fd)
        Some(boolAST(f(asElems(0), asElems(1))))
      } else if(functions2Rev.isDefinedAt(fd)) {
        assert(args.size == 2)
        val f = functions2Rev(fd)
        Some(constant(f(asElems(0), asElems(1))))      
      } else if(predicates3Rev.isDefinedAt(fd)) {
        assert(args.size == 3)
        val f = predicates3Rev(fd)
        Some(boolAST(f(asElems(0), asElems(1), asElems(2))))
      } else if(functions3Rev.isDefinedAt(fd)) {
        assert(args.size == 3)
        val f = functions3Rev(fd)
        Some(constant(f(asElems(0), asElems(1), asElems(2))))
      } else {
        error("`interpret' was called with an unknown Z3FuncDecl: " + fd)
      }
    } else {
      None
    }
  }

  setCallbacks(
    reduceApp = true,
    newAssignment = true,
    newEq = true,
    finalCheck = true
  )

  //showCallbacks(true)

  override def reduceApp(fd : Z3FuncDecl, args : Z3AST*) : Option[Z3AST] = if(args.isEmpty) None else interpret(fd, (args.asInstanceOf[Seq[Z3AST]]) : _*)

  override def newAssignment(pred: Z3AST, polarity: Boolean) : Unit = {
    context.getASTKind(pred) match {
      case Z3AppAST(fd, args) if allPredicates(fd) => treatAssignment(fd, args : _*)
      case _ => 
    }
  }

  override def newEq(t1 : Z3AST, t2 : Z3AST) : Unit = {
    getEqClassValue(t1) match {
      case Some(v1) => applyAxiomsForParentsOf(t2.asInstanceOf[Z3AST], v1)
      case None => 
    }
    getEqClassValue(t2) match {
      case Some(v2) => applyAxiomsForParentsOf(t1.asInstanceOf[Z3AST], v2)
      case None =>
    }
  }

  override def finalCheck : Boolean = {
    var toReturn = true

    for(curr <- getApps) context.getASTKind(curr) match {
      case Z3AppAST(fd, args) if allPredicates(fd) => toReturn = toReturn & treatAssignment(fd, args : _*)
      case Z3AppAST(fd, args) if allFunctions(fd) => {
        if(getEqClassValue(curr).isEmpty) {
          toReturn = toReturn & treatApplication(fd, args : _*)  
        }
      }
      case _ => ;
    }

    toReturn
  }

  /** Analyzes the assignment, returns true if an axiom could be asserted that
   * determines the truth value of the application. */
  private def treatAssignment(fd: Z3FuncDecl, args: Z3AST*) : Boolean = {
    val valArgs : Seq[Option[Z3AST]] = (args.asInstanceOf[Seq[Z3AST]]).map(getEqClassValue(_))
    if(valArgs.forall(_.isDefined)) {
      val valArgs2 : Seq[Z3AST] = valArgs.map(_.get)
      val result : Option[Z3AST] = interpret(fd, valArgs2 : _*)
      result match {
        case Some(b) => assertAxiomProxy(context.mkIff(b, fd(valArgs2 : _*))); true
        case None => false
      }
    } else {
      false
    }
  }

  /** Analyzes the application, returns true if an axiom could be asserted that
   * determines the value of the application. */
  private def treatApplication(fd: Z3FuncDecl, args: Z3AST*) : Boolean = {
    val valArgs : Seq[Option[Z3AST]] = (args.asInstanceOf[Seq[Z3AST]]).map(getEqClassValue(_))
    if(valArgs.forall(_.isDefined)) {
      val valArgs2 : Seq[Z3AST] = valArgs.map(_.get)
      val result : Option[Z3AST] = interpret(fd, valArgs2 : _*)
      result match {
        case Some(v) => assertAxiomProxy(context.mkEq(v, fd(valArgs2 : _*))); true
        case None => false
      }
    } else {
      false
    }
  }

  /** Called when we just figured out that n was equal to the constant value v.
   * We will traverse all function/predicate applications that have n as an
   * argument and check whether some of them just became ground. */
   private def applyAxiomsForParentsOf(n : Z3AST, v: Z3AST) : Unit = {
    val root = getEqClassRoot(n)
    for(nPrime <- getEqClassMembers(n); parent <- getParents(nPrime)) context.getASTKind(parent) match {
      case Z3AppAST(fd, args) if allPredicates(fd) || allFunctions(fd) => {
        val newArgs : Seq[Option[Z3AST]] = args.map(a => {
          if(getEqClassRoot(a.asInstanceOf[Z3AST]) == root)
            Some(v.asInstanceOf[Z3AST])
          else
            getEqClassValue(a.asInstanceOf[Z3AST])
        })
        if(newArgs.forall(_.isDefined)) {
          val newArgs2 = newArgs.map(_.get)
          val result = interpret(fd, newArgs2 : _*)
          result match {
            case Some(ast) => assertAxiomProxy(context.mkEq(fd(newArgs2 : _*), ast))
            case _ => ;
          }
        }
      }
      case _ => ;
    }
  }

  private def assertAxiomProxy(axiom : Z3AST) : Unit = {
    //println("Asserting now : " + axiom)
    assertAxiom(axiom)
  }

  private def isTheoryConstant(a : Z3AST) : Boolean = {
    val result = isTheoryValue(a) && constantsRev.isDefinedAt(a.asInstanceOf[Z3AST])
    result
  }

  /** For a given AST, tries to find one in the same equivalence class that represents
   * a known value. */
  private def getEqClassValue(n: Z3AST) : Option[Z3AST] = {
    val members = getEqClassMembers(n.asInstanceOf[Z3AST])
    val result = members.find(isTheoryConstant(_))
    result
  }
}
