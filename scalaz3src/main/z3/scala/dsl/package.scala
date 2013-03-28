package z3.scala

package object dsl {
  import Operands._

  class UnsatisfiableConstraintException extends Exception
  class SortMismatchException(msg : String) extends Exception("Sort mismatch: " + msg)

  implicit def z3ASTToBoolOperand(ast : Z3AST) : BoolOperand = {
    if(!ast.getSort.isBoolSort) {
      throw new SortMismatchException("expected boolean operand, got: " + ast)
    }
    new BoolOperand(Z3ASTWrapper[BoolSort](ast))
  }

  implicit def booleanValueToBoolTree(value : Boolean) : Tree[BoolSort] = BoolConstant(value)

  implicit def booleanValueToBoolOperand(value : Boolean) : BoolOperand = new BoolOperand(BoolConstant(value))

  implicit def boolTreeToBoolOperand[T >: BottomSort <: BoolSort](tree : Tree[T]) : BoolOperand =
    new BoolOperand(tree)

  implicit def boolOperandToBoolTree(operand : BoolOperand) : Tree[BoolSort] = operand.tree.asInstanceOf[Tree[BoolSort]]

  implicit def z3ASTToIntOperand(ast : Z3AST) : IntOperand = {
    if(!ast.getSort.isIntSort) {
      throw new SortMismatchException("expected integer operand, got: " + ast)
    }
    new IntOperand(Z3ASTWrapper[IntSort](ast))
  }

  implicit def intValueToIntTree(value : Int) : Tree[IntSort] = IntConstant(value)

  implicit def intValueToIntOperand(value : Int) : IntOperand = new IntOperand(IntConstant(value))

  implicit def intTreeToIntOperand[T >: BottomSort <: IntSort](tree : Tree[T]) : IntOperand =
    new IntOperand(tree)

  implicit def intOperandToIntTree(operand : IntOperand) : Tree[IntSort] = operand.tree.asInstanceOf[Tree[IntSort]]

  implicit def z3ASTToSetOperand(ast : Z3AST) : SetOperand = {
    // TODO how do we check the type (set of any type?) here?
    new SetOperand(Z3ASTWrapper[SetSort](ast))
  }

  implicit def intSetValueToSetTree(value : Set[Int]) : Tree[SetSort] = {
    value.foldLeft[Tree[SetSort]](EmptyIntSet())((set, elem) => SetAdd(set, IntConstant(elem)))
  }

  implicit def intSetValueToSetOperand(value : Set[Int]) : SetOperand = {
    new SetOperand(intSetValueToSetTree(value))
  }

  implicit def setTreeToSetOperand[T >: BottomSort <: SetSort](tree : Tree[T]) : SetOperand =
    new SetOperand(tree)

  implicit def setOperandToSetTree(operand : SetOperand) : Tree[SetSort] = operand.tree.asInstanceOf[Tree[SetSort]]

  // Predefined ValHandler's

  implicit object BooleanValHandler extends ValHandler[Boolean] {
    def mkSort(z3 : Z3Context) : Z3Sort = z3.mkBoolSort

    def convert(model : Z3Model, ast : Z3AST) : Boolean =
      model.evalAs[Boolean](ast).getOrElse(false)
  }

  implicit object IntValHandler extends ValHandler[Int] {
    def mkSort(z3 : Z3Context) : Z3Sort = z3.mkIntSort

    def convert(model : Z3Model, ast : Z3AST) : Int =
      model.evalAs[Int](ast).getOrElse(0)
  }

  implicit def liftToSetValHander[A : Default : ValHandler] : ValHandler[Set[A]] = new ValHandler[Set[A]] {
    private val underlying = implicitly[ValHandler[A]]

    def mkSort(z3 : Z3Context) : Z3Sort = z3.mkSetSort(underlying.mkSort(z3))

    def convert(model : Z3Model, ast : Z3AST) : Set[A] = {
      model.eval(ast) match {
        case None => default.value // when not in model, we assume anything is OK
        case Some(evaluated) => model.getSetValue(evaluated) match {
          case Some(astSet) => astSet.map(a => underlying.convert(model, a)).toSet
          case None => default.value
        }
      }
    }  
  }

  /** Instances of this class are used to represent models of Z3 maps, which
   * are typically defined by a finite collection of pairs and a default
   * value. More sophisticated representations à la functional programs that
   * can sometimes be obtained from quantified formulas are not yet
   * supported. PS. */
  class PointWiseFunction[-A,+B](points: Map[A,B], default: B) extends (A=>B) {
    def apply(a : A) : B = points.getOrElse(a, default)
  }
  implicit def liftToFuncHandler[A : Default : ValHandler, B : Default : ValHandler] : ValHandler[A=>B] = new ValHandler[A=>B] {
    private val underlyingA = implicitly[ValHandler[A]]
    private val underlyingB = implicitly[ValHandler[B]]

    def mkSort(z3 : Z3Context) : Z3Sort =
      z3.mkArraySort(underlyingA.mkSort(z3), underlyingB.mkSort(z3))

    def convert(model : Z3Model, ast : Z3AST) : (A=>B) = {
      model.eval(ast) match {
        case None => default.value
        case Some(evaluated) => model.getArrayValue(evaluated) match {
          case Some((mp,dflt)) => {
            new PointWiseFunction[A,B](
              mp.map(kv => (underlyingA.convert(model,kv._1), underlyingB.convert(model,kv._2))),
              underlyingB.convert(model,dflt)
            )
          }
          case None => default.value
        }
      }
    }
  }

  def choose[T:ValHandler](predicate : Val[T] => Tree[BoolSort]) : T = find(predicate) match {
    case Some(result) => result
    case None => throw new UnsatisfiableConstraintException
  }

  def find[T:ValHandler](predicate : Val[T] => Tree[BoolSort]) : Option[T] = {
    val z3 = new Z3Context("MODEL" -> true)
    val solver = z3.mkSolver
    val vh = implicitly[ValHandler[T]]
    val valTree = vh.construct
    val valAST = valTree.ast(z3)
    val constraintTree = predicate(valTree)
    solver.assertCnstr(constraintTree.ast(z3))
    solver.checkAndGetModel match {
      case (Some(true), m) => {
        val result = vh.convert(m, valAST)
        z3.delete
        Some(result)
      }
      case (_, m) => {
        z3.delete
        None
      }
    }
  }

  def findAll[T:ValHandler](predicate : Val[T] => Tree[BoolSort]) : Iterator[T] = {
    val z3 = new Z3Context("MODEL" -> true)
    val solver = z3.mkSolver
    val vh = implicitly[ValHandler[T]]
    val valTree = vh.construct
    val valAST = valTree.ast(z3)
    val constraintTree = predicate(valTree)

    solver.assertCnstr(constraintTree.ast(z3))
    solver.checkAndGetAllModels.map(m => {
      val result = vh.convert(m, valAST)
      result
    })
  }

  def choose[T1:ValHandler,T2:ValHandler](predicate : (Val[T1],Val[T2]) => Tree[BoolSort]) : (T1,T2) = find(predicate) match {
    case Some(p) => p
    case None => throw new UnsatisfiableConstraintException
  }

  def find[T1:ValHandler,T2:ValHandler](predicate : (Val[T1],Val[T2]) => Tree[BoolSort]) : Option[(T1,T2)] = {
    val z3 = new Z3Context("MODEL" -> true)
    val solver = z3.mkSolver
    val vh1 = implicitly[ValHandler[T1]]
    val vh2 = implicitly[ValHandler[T2]]
    val valTree1 = vh1.construct
    val valTree2 = vh2.construct
    val valAST1 = valTree1.ast(z3)
    val valAST2 = valTree2.ast(z3)
    val constraintTree = predicate(valTree1,valTree2)
    solver.assertCnstr(constraintTree.ast(z3))
    solver.checkAndGetModel match {
      case (Some(true), m) => {
        val result1 = vh1.convert(m, valAST1)
        val result2 = vh2.convert(m, valAST2)
        z3.delete
        Some((result1,result2))
      }
      case (_, m) => {
        z3.delete
        None
      }
    }
  }

  def findAll[T1:ValHandler,T2:ValHandler](predicate : (Val[T1],Val[T2]) => Tree[BoolSort]) : Iterator[(T1,T2)] = {
    val z3 = new Z3Context("MODEL" -> true)
    val solver = z3.mkSolver
    val vh1 = implicitly[ValHandler[T1]]
    val vh2 = implicitly[ValHandler[T2]]
    val valTree1 = vh1.construct
    val valTree2 = vh2.construct
    val valAST1 = valTree1.ast(z3)
    val valAST2 = valTree2.ast(z3)
    val constraintTree = predicate(valTree1, valTree2)

    solver.assertCnstr(constraintTree.ast(z3))
    solver.checkAndGetAllModels.map(m => {
      val result1 = vh1.convert(m, valAST1)
      val result2 = vh2.convert(m, valAST2)
      (result1,result2)
    })
  }

  def choose[T1:ValHandler,T2:ValHandler,T3:ValHandler](predicate : (Val[T1],Val[T2],Val[T3]) => Tree[BoolSort]) : (T1,T2,T3) = find(predicate) match {
    case Some(p) => p
    case None => throw new UnsatisfiableConstraintException
  }

  def find[T1:ValHandler,T2:ValHandler,T3:ValHandler](predicate : (Val[T1],Val[T2],Val[T3]) => Tree[BoolSort]) : Option[(T1,T2,T3)] = {
    val z3 = new Z3Context("MODEL" -> true)
    val solver = z3.mkSolver
    val vh1 = implicitly[ValHandler[T1]]
    val vh2 = implicitly[ValHandler[T2]]
    val vh3 = implicitly[ValHandler[T3]]
    val valTree1 = vh1.construct
    val valTree2 = vh2.construct
    val valTree3 = vh3.construct
    val valAST1 = valTree1.ast(z3)
    val valAST2 = valTree2.ast(z3)
    val valAST3 = valTree3.ast(z3)
    val constraintTree = predicate(valTree1,valTree2, valTree3)
    solver.assertCnstr(constraintTree.ast(z3))
    solver.checkAndGetModel match {
      case (Some(true), m) => {
        val result1 = vh1.convert(m, valAST1)
        val result2 = vh2.convert(m, valAST2)
        val result3 = vh3.convert(m, valAST3)
        z3.delete
        Some((result1,result2,result3))
      }
      case (_, m) => {
        z3.delete
        None
      }
    }
  }

  def findAll[T1:ValHandler,T2:ValHandler,T3:ValHandler](predicate : (Val[T1],Val[T2],Val[T3]) => Tree[BoolSort]) : Iterator[(T1,T2,T3)] = {
    val z3 = new Z3Context("MODEL" -> true)
    val solver = z3.mkSolver

    val vh1 = implicitly[ValHandler[T1]]
    val vh2 = implicitly[ValHandler[T2]]
    val vh3 = implicitly[ValHandler[T3]]
    val valTree1 = vh1.construct
    val valTree2 = vh2.construct
    val valTree3 = vh3.construct
    val valAST1 = valTree1.ast(z3)
    val valAST2 = valTree2.ast(z3)
    val valAST3 = valTree3.ast(z3)
    val constraintTree = predicate(valTree1, valTree2, valTree3)

    solver.assertCnstr(constraintTree.ast(z3))
    solver.checkAndGetAllModels.map(m => {
      val result1 = vh1.convert(m, valAST1)
      val result2 = vh2.convert(m, valAST2)
      val result3 = vh3.convert(m, valAST3)
      (result1,result2,result3)
    })
  }
}
