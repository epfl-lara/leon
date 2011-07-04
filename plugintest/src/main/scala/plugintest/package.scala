package object plugintest {
  trait MyAny

  sealed trait IsMyAny[T] {
    val manifest : ClassManifest[T]
  }

  implicit def isMyAny[T <: MyAny : ClassManifest] = new IsMyAny[T] {
    val manifest = implicitly[ClassManifest[T]]
  }

  implicit object IntIsMyAny extends IsMyAny[Int] {
    val manifest = implicitly[ClassManifest[Int]]
  }

  implicit object BooleanIsMyAny extends IsMyAny[Boolean] {
    val manifest = implicitly[ClassManifest[Boolean]]
  }
}
