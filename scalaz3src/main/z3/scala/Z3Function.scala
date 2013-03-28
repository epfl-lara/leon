package z3.scala

sealed class Z3Function(private val interpretation: (Seq[(Seq[Z3AST], Z3AST)], Z3AST)) {
  private lazy val iMap = interpretation._1.toMap

  val arity = interpretation._1.head._1.size

  def apply(args: Z3AST*) = {
    assert(args.size == arity, "function call with wrong number of arguments")
    iMap.get(args) match {
      case Some(res) => res
      case None => interpretation._2
    }
  }
}

