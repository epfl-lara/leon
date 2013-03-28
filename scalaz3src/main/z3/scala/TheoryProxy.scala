package z3.scala

import z3.{Z3Wrapper,Pointer,AbstractTheoryProxy}

/** This class serves as a router for calls from Z3 to the Scala <code>Z3Theory</code> 
 * instances. Instances of <code>TheoryProxy</code> are automatically created and should not
 * be managed by the user. Their methods should not be called manually. */
sealed class TheoryProxy private[z3](context: Z3Context, thy: Z3Theory) extends AbstractTheoryProxy {
  private var sc: Boolean = false
  private var sp: String = ""

  final def showCalls(show: Boolean, prefix: String) : Unit = {
    sc = show
    sp = prefix
  }

  private def msg(name: String, args: Any*) : Unit = if(sc) {
    if(args.isEmpty) {
      println("In theory " + sp + ": " + name + " was called.")
    } else {
      println("In theory " + sp + ": " + name + " was called with args :")
      println(args.toSeq.toList.mkString("  ", ",\n  ", ""))
    }
  }

  def delete(tPtr: Long) : Unit = {
    msg("delete")
    thy.delete
  }
  def reduceEq(tPtr: Long, t1: Long, t2: Long, out: Pointer) : Boolean = {
    val a1 = new Z3AST(t1, context)
    val a2 = new Z3AST(t2, context)
    msg("reduceEq", a1, a2)
    thy.reduceEq(a1, a2) match {
      case Some(ast) => out.ptr = ast.ptr; true
      case None => false
    } 
  }
  def reduceApp(tPtr: Long, fdPtr: Long, argc: Int, args: Array[Long], out: Pointer) : Boolean = {
    val fd = new Z3FuncDecl(fdPtr, Z3Wrapper.getDomainSize(context.ptr, fdPtr), context);
    val aa = args.map(new Z3AST(_, context)) 
    msg("reduceApp", (fd +: aa) : _*)
    thy.reduceApp(fd, aa : _*) match {
      case Some(ast) => out.ptr = ast.ptr; true
      case None => false
    }
  }
  def reduceDistinct(tPtr: Long, argc: Int, args: Array[Long], out: Pointer) : Boolean = {
    val aa = args.map(new Z3AST(_, context))
    msg("reduceDistinct", aa : _*)
    thy.reduceDistinct(aa : _*) match {
      case Some(ast) => out.ptr = ast.ptr; true
      case None => false
    }
  }
  def newApp(tPtr: Long, appPtr: Long) : Unit = {
    val a = new Z3AST(appPtr, context)
    msg("newApp", a)
    thy.newApp(a)
  }
  def newElem(tPtr: Long, elemPtr: Long) : Unit = {
    val a = new Z3AST(elemPtr, context)
    msg("newElem", a)
    thy.newElem(a)
  }
  def initSearch(tPtr: Long) : Unit = {
    msg("initSearch")
    thy.initSearch
  }
  def push(tPtr: Long) : Unit = {
    msg("push")
    thy.push
  }
  def pop(tPtr: Long) : Unit = {
    msg("pop")
    thy.pop
  }
  def restart(tPtr: Long) : Unit = {
    msg("restart")
    thy.restart
  }
  def reset(tPtr: Long) : Unit = {
    msg("reset")
    thy.reset
  }
  def finalCheck(tPtr: Long) : Boolean = {
    msg("finalCheck")
    thy.finalCheck
  }
  def newEq(tPtr: Long, t1: Long, t2: Long) : Unit = {
    val a1 = new Z3AST(t1, context)
    val a2 = new Z3AST(t2, context)
    msg("newEq", a1, a2)
    thy.newEq(a1, a2)
  }
  def newDiseq(tPtr: Long, t1: Long, t2: Long) : Unit = {
    val a1 = new Z3AST(t1, context)
    val a2 = new Z3AST(t2, context)
    msg("newDiseq", a1, a2)
    thy.newDiseq(a1, a2)
  }
  def newAssignment(tPtr: Long, pred: Long, polarity: Boolean) : Unit = {
    val a = new Z3AST(pred, context)
    msg("newAssignment", a, polarity)
    thy.newAssignment(a, polarity)
  }
  def newRelevant(tPtr: Long, t: Long) : Unit = {
    val a = new Z3AST(t, context)
    msg("newRelevant", a)
    thy.newRelevant(a)
  }
}
