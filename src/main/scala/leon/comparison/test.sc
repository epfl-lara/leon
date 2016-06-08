val x: Option[Char] = None
val y: Option[Char] = Option('b')

val list = List(x, y)

list map(_.get)
