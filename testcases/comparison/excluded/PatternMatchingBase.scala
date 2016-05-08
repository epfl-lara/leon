object PatternMatchingBase {
  abstract class A
  case class B(x: Int) extends A

  val foo = List(1)

  def class_B(x: Int): B = B(x)

  val listOneElement = List(1)


  def inversed_match_value(x: Int): Char = x match {
    case 2 => 'b'
    case 1 => 'a'
  }


  def encapsulated_match_value(x: Int): Char = x match {
    case x2 if x2 < 10 =>
      x2 match {
        case 1 => 'a'
        case 2 => 'b'
      }
    case _ => 'z'
  }


/*
  def match_value(x: Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
  }

  def encapsulated_match_value(x: Int): Char = x match {
    case x2 if x2 < 10 =>
      x2 match {
        case 1 => 'a'
        case 2 => 'b'
      }
    case _ => 'z'
  }

  def inversed_match_value(x: Int): Char = x match {
    case 2 => 'b'
    case 1 => 'a'
  }


  /**
    * The normalization... DOESN'T NORMALIZE THE TYPE !
    */
  def match_subclass(x: List[Int]): Char = x match {
    case Cons(x, xs) => 'a'
    case Nil() => 'b'
  }
*/

  val listOneElement = List(1)

  val listOneElement_2 = List(2)



}
