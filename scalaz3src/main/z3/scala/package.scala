package z3

package object scala {
  def toggleWarningMessages(enabled: Boolean) : Unit = {
    Z3Wrapper.toggleWarningMessages(enabled)
  }

  def resetMemory : Unit = {
    Z3Wrapper.resetMemory()
  }

  /** A string representation of the version numbers for Z3, and the API (including bindings) */
  lazy val version : String = {
    Z3Wrapper.z3VersionString() + ", " + Z3Wrapper.wrapperVersionString()
  }

  protected[z3] def toPtrArray(ptrs : Iterable[{ def ptr : Long }]) : Array[Long] = {
    ptrs.map(_.ptr).toArray
  }

  protected[z3] def i2ob(value: Int) : Option[Boolean] = value match {
    case -1 => Some(false)
    case 0 => None
    case _ => Some(true)
  }


  def error(any : Any) : Nothing = {
    //Predef.error(any.toString)
    sys.error(any.toString) // 2.9
  }

  // All default values

  implicit object DefaultInt extends Default[Int] {
    val value = 0
  }

  implicit object DefaultBoolean extends Default[Boolean] {
    val value = true
  }

  implicit def liftDefaultToSet[A : Default] : Default[Set[A]] = {
    new Default[Set[A]] {
      val value = Set.empty[A]
    }
  }

  implicit def liftDefaultToFun[A,B : Default] : Default[A=>B] = {
    new Default[A=>B] {
      val value = ((a : A) => implicitly[Default[B]].value)
    }
  }

  implicit def astvectorToSeq(v: Z3ASTVector): Seq[Z3AST] = v.toSeq
}
