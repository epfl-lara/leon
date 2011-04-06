package cp

object Definitions {
  final class NotImplementedException extends Exception

  def choose[A](pred : A => Boolean) : A = {
    throw new NotImplementedException()
  }

  def choose[A,B](pred : (A,B) => Boolean) : (A,B) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C](pred : (A,B,C) => Boolean) : (A,B,C) = {
    throw new NotImplementedException()
  }
}
