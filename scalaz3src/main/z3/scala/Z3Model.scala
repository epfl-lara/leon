package z3.scala

import z3.{Z3Wrapper,Pointer}

object Z3Model {
  implicit def ast2int(model: Z3Model, ast: Z3AST): Option[Int] = {
    val res = model.eval(ast)
    if (res.isEmpty)
      None
    else
      model.context.getNumeralInt(res.get).value
  }

  implicit def ast2bool(model: Z3Model, ast: Z3AST): Option[Boolean] = {
    val res = model.eval(ast)
    if (res.isEmpty)
      None
    else
      model.context.getBoolValue(res.get)
  }

  implicit def ast2intSet(model: Z3Model, ast: Z3AST) : Option[Set[Int]] = model.eval(ast) match {
    case None => None
    case Some(evaluated) => model.getSetValue(evaluated) match {
      case Some(astSet) =>
        Some(astSet.map(elem => model.evalAs[Int](elem)).foldLeft(Set[Int]())((acc, e) => e match {
          case Some(value) => acc + value
          case None => acc
        }))
      case None => None
    }
  }
}

sealed class Z3Model private[z3](val ptr: Long, val context: Z3Context) extends Z3Object {
  override def toString : String = context.modelToString(this)

  @deprecated("Z3Model.delete() not be used, use incref/decref instead", "")
  def delete: Unit = {
  }

  def incRef() {
    Z3Wrapper.modelIncRef(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.modelDecRef(context.ptr, this.ptr)
  }

  def eval(ast: Z3AST, completion: Boolean = false) : Option[Z3AST] = {
    if(this.ptr == 0L) {
      throw new IllegalStateException("The model is not initialized.")
    }
    val out = new Pointer(0L)
    val result = Z3Wrapper.modelEval(context.ptr, this.ptr, ast.ptr, out, completion)
    if (result) {
      Some(new Z3AST(out.ptr, context))
    } else {
      None
    }
  }

  def evalAs[T](input: Z3AST)(implicit converter: (Z3Model, Z3AST) => Option[T]): Option[T] = {
    converter(this, input)
  }

  def getModelConstants: Iterator[Z3FuncDecl] = {
    val model = this
    new Iterator[Z3FuncDecl] {
      val total: Int = Z3Wrapper.getModelNumConstants(context.ptr, model.ptr)
      var returned: Int = 0

      override def hasNext: Boolean = (returned < total)
      override def next(): Z3FuncDecl = {
        val toReturn = new Z3FuncDecl(Z3Wrapper.getModelConstant(context.ptr, model.ptr, returned), 0, context)
        returned += 1
        toReturn
      }
    }
  }

  def getModelConstantInterpretations : Iterator[(Z3FuncDecl, Z3AST)] = {
    val model = this
    val constantIterator = getModelConstants
    new Iterator[(Z3FuncDecl, Z3AST)] {
      override def hasNext: Boolean = constantIterator.hasNext
      override def next(): (Z3FuncDecl, Z3AST) = {
        val nextConstant = constantIterator.next()
        (nextConstant, model.eval(nextConstant()).get)
      }
    }
  }

  private lazy val constantInterpretationMap: Map[String, Z3AST] =
   getModelConstantInterpretations.map(p => (p._1.getName.toString, p._2)).toMap

  def getModelConstantInterpretation(name: String): Option[Z3AST] =
    constantInterpretationMap.get(name) match {
      case None => None
      case Some(v) => Some(v.asInstanceOf[Z3AST])
    }

  def getModelFuncInterpretations : Iterator[(Z3FuncDecl, Seq[(Seq[Z3AST], Z3AST)], Z3AST)] = {
    val model = this
    new Iterator[(Z3FuncDecl, List[(List[Z3AST], Z3AST)], Z3AST)] {
      val total: Int = Z3Wrapper.getModelNumFuncs(context.ptr, model.ptr)
      var returned: Int = 0

      override def hasNext: Boolean = (returned < total)
      override def next(): (Z3FuncDecl, List[(List[Z3AST], Z3AST)], Z3AST) = {
        val declPtr = Z3Wrapper.getModelFuncDecl(context.ptr, model.ptr, returned)
        val arity = Z3Wrapper.getDomainSize(context.ptr, declPtr)
        val funcDecl = new Z3FuncDecl(declPtr, arity, context)
        val numEntries = Z3Wrapper.getModelFuncNumEntries(context.ptr, model.ptr, returned)
        val entries = for (entryIndex <- 0 until numEntries) yield {
          val numArgs = Z3Wrapper.getModelFuncEntryNumArgs(context.ptr, model.ptr, returned, entryIndex)
          val arguments = for (argIndex <- 0 until numArgs) yield {
            new Z3AST(Z3Wrapper.getModelFuncEntryArg(context.ptr, model.ptr, returned, entryIndex, argIndex), context)
          }
          (arguments.toList, new Z3AST(Z3Wrapper.getModelFuncEntryValue(context.ptr, model.ptr, returned, entryIndex), context))
        }
        val elseValue = new Z3AST(Z3Wrapper.getModelFuncElse(context.ptr, model.ptr, returned), context)
        returned += 1
        (funcDecl, entries.toList, elseValue)
      }
    }
  }

  private lazy val funcInterpretationMap: Map[Z3FuncDecl, (Seq[(Seq[Z3AST], Z3AST)], Z3AST)] =
    getModelFuncInterpretations.map(i => (i._1, (i._2, i._3))).toMap

  def isArrayValue(ast: Z3AST) : Option[Int] = {
    val numEntriesPtr = new Z3Wrapper.IntPtr()
    val result = Z3Wrapper.isArrayValue(context.ptr, this.ptr, ast.ptr, numEntriesPtr)
    if (result) {
      Some(numEntriesPtr.value)
    } else {
      None
    }
  }

  def getArrayValue(ast: Z3AST) : Option[(Map[Z3AST, Z3AST], Z3AST)] = isArrayValue(ast) match {
    case None => None
    case Some(numEntries) =>
      val indArray = new Array[Long](numEntries)
      val valArray = new Array[Long](numEntries)
      val elseValuePtr = new Pointer(0L)

      Z3Wrapper.getArrayValue(context.ptr, this.ptr, ast.ptr, numEntries, indArray, valArray, elseValuePtr)

      val elseValue = new Z3AST(elseValuePtr.ptr, context)
      val map = Map((indArray.map(new Z3AST(_, context)) zip valArray.map(new Z3AST(_, context))): _*)
      Some((map, elseValue))
  }

  def getSetValue(ast: Z3AST) : Option[Set[Z3AST]] = this.getArrayValue(ast) match {
    case None => None
    case Some((map, elseValue)) =>
      Some(map.filter(pair => context.getBoolValue(pair._2) == Some(true)).keySet.toSet)
  }

  /* FOR VERSIONS 2.X WHERE 15 <= X <= 19 */
  def getArrayValueOld(ast: Z3AST) : Option[(Map[Z3AST, Z3AST], Z3AST)] = context.getASTKind(ast) match {
    case Z3AppAST(decl, args) => funcInterpretationMap.get(context.getDeclFuncDeclParameter(decl, 0)) match {
      case Some((entries, elseValue)) =>
        assert(entries.forall(_._1.size == 1))
        val asMap = entries.map {
          case (arg :: Nil, value) => (arg, value)
        }.toMap
        Some(asMap, elseValue)
      case None => None
    }
    case _ => None
  }

  def getModelFuncInterpretation(fd: Z3FuncDecl): Option[Z3Function] = {
    funcInterpretationMap.find(i => i._1 == fd) match {
      case Some(i) => Some(new Z3Function(i._2))
      case None => None
    }
  }

  locally {
    context.modelQueue.incRef(this)
  }

  override def finalize() {
    context.modelQueue.decRef(this)
  }
}
