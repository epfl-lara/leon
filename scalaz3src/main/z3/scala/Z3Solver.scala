package z3.scala

import z3.Z3Wrapper

class Z3Solver private[z3](val ptr : Long, val context : Z3Context) extends Z3Object {
  override def equals(that : Any) : Boolean = {
    that != null &&
      that.isInstanceOf[Z3Solver] && {
      val that2 = that.asInstanceOf[Z3Solver]
      that2.ptr == this.ptr // && context.isEqAST(this, that2)
    }
  }

  def pop(numScopes : Int = 1) = {
    Z3Wrapper.solverPop(context.ptr, this.ptr, numScopes)
  }

  def push() = {
    Z3Wrapper.solverPush(context.ptr, this.ptr)
  }

  var isModelAvailable = false

  def assertCnstr(ast: Z3AST) = {
    Z3Wrapper.solverAssertCnstr(context.ptr, this.ptr, ast.ptr)
  }

  def check() : Option[Boolean] = {
    val res = i2ob(Z3Wrapper.solverCheck(context.ptr, this.ptr))
    isModelAvailable = res != Some(false)
    res
  }

  def getAssertions(): Z3ASTVector = {
    new Z3ASTVector(Z3Wrapper.solverGetAssertions(context.ptr, this.ptr), context)
  }

  def getModel() : Z3Model = {
    if (isModelAvailable) {
      new Z3Model(Z3Wrapper.solverGetModel(context.ptr, this.ptr), context)
    } else {
      throw new Exception("Cannot get model if check failed")
    }
  }

  def getUnsatCore() : Z3ASTVector = {
    new Z3ASTVector(Z3Wrapper.solverGetUnsatCore(context.ptr, this.ptr), context)
  }

  def reset() = {
    Z3Wrapper.solverReset(context.ptr, this.ptr)
  }

  def getNumScopes() = {
    Z3Wrapper.solverGetNumScopes(context.ptr, this.ptr)  
  }

  def incRef() {
    Z3Wrapper.solverIncRef(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.solverDecRef(context.ptr, this.ptr)
  }

  def checkAssumptions(assumptions: Z3AST*) : Option[Boolean] = {
    val res = i2ob(
      Z3Wrapper.solverCheckAssumptions(
        context.ptr,
        this.ptr,
        assumptions.size,
        toPtrArray(assumptions)
      )
    )

    isModelAvailable = res != Some(false)
    res
  }

  // Utility functions that should no longer be exposed
  private[z3] def checkAndGetModel() = {
    (check(), if (isModelAvailable) getModel() else null)
  }

  private[z3] def checkAssumptionsGetModelOrCore(assumptions: Z3AST*) = {
    (checkAssumptions(assumptions : _*), if (isModelAvailable) getModel() else null, getUnsatCore())
  }

  private[z3] def assertCnstr(tree : dsl.Tree[dsl.BoolSort]) : Unit = {
    assertCnstr(tree.ast(context))
  }

  private[z3] def checkAndGetAllModels(): Iterator[Z3Model] = {
    new Iterator[Z3Model] {
      var constraints: Z3AST = context.mkTrue
      var nextModel: Option[Option[Z3Model]] = None
      
      override def hasNext: Boolean =  nextModel match {
        case None =>
          // Check whether there are any more models
          push()
          assertCnstr(constraints)
          val result = checkAndGetModel()
          pop(1)
          val toReturn = (result match {
            case (Some(true), m) =>
              nextModel = Some(Some(m))
              val newConstraints = m.getModelConstantInterpretations.foldLeft(context.mkTrue){
                (acc, s) => context.mkAnd(acc, context.mkEq(s._1(), s._2))
              }
              constraints = context.mkAnd(constraints, context.mkNot(newConstraints))
              true
            case (Some(false), _) =>
              nextModel = Some(None)
              false
            case (None, _) =>
              nextModel = Some(None)
              false
          })
          toReturn
        case Some(None) => false
        case Some(Some(m)) => true
      }

      override def next(): Z3Model = nextModel match {
        case None =>
          // Compute next model
          push()
          assertCnstr(constraints)
          val result = checkAndGetModel()
          pop(1)
          val toReturn = (result match {
            case (Some(true), m) =>
              val newConstraints = m.getModelConstantInterpretations.foldLeft(context.mkTrue){
                (acc, s) => context.mkAnd(acc, context.mkEq(s._1(), s._2))
              }
              constraints = context.mkAnd(constraints, context.mkNot(newConstraints))
              m
            case _ =>
              throw new Exception("Requesting a new model while there are no more models.")
          })
          toReturn
        case Some(Some(m)) => 
          nextModel = None
          m
        case Some(None) => throw new Exception("Requesting a new model while there are no more models.")
      }
    }
  }

  private[z3] def checkAndGetAllEventualModels(): Iterator[(Option[Boolean], Z3Model)] = {
    new Iterator[(Option[Boolean], Z3Model)] {
      var constraints: Z3AST = context.mkTrue
      var nextModel: Option[Option[(Option[Boolean],Z3Model)]] = None
      
      override def hasNext: Boolean =  nextModel match {
        case None =>
          // Check whether there are any more models
          push()
          assertCnstr(constraints)
          val result = checkAndGetModel()
          pop(1)
          val toReturn = (result match {
            case (Some(false), _) =>
              nextModel = Some(None)
              false
            case (outcome, m) =>
              nextModel = Some(Some((outcome, m)))
              val newConstraints = m.getModelConstantInterpretations.foldLeft(context.mkTrue){
                (acc, s) => context.mkAnd(acc, context.mkEq(s._1(), s._2))
              }
              constraints = context.mkAnd(constraints, context.mkNot(newConstraints))
              true
          })
          toReturn
        case Some(None) => false
        case Some(Some(_)) => true
      }

      override def next(): (Option[Boolean], Z3Model) = nextModel match {
        case None =>
          // Compute next model
          push()
          assertCnstr(constraints)
          val result = checkAndGetModel()
          pop(1)
          val toReturn = (result match {
            case (Some(false), _) =>
              throw new Exception("Requesting a new model while there are no more models.")
            case (outcome, m) =>
              val newConstraints = m.getModelConstantInterpretations.foldLeft(context.mkTrue){
                (acc, s) => context.mkAnd(acc, context.mkEq(s._1(), s._2))
              }
              constraints = context.mkAnd(constraints, context.mkNot(newConstraints))
              (outcome, m)
          })
          toReturn
        case Some(Some((outcome, m))) => 
          nextModel = None
          (outcome, m)
        case Some(None) => throw new Exception("Requesting a new model while there are no more models.")
      }
    }
  }

  def getReasonUnknown() : String = {
    Z3Wrapper.solverGetReasonUnknown(context.ptr, this.ptr)
  }

  override def toString() : String = {
    Z3Wrapper.solverToString(context.ptr, this.ptr)
  }

  locally {
    context.solverQueue.incRef(this)
  }

  override def finalize() {
    context.solverQueue.decRef(this)
  }
}
