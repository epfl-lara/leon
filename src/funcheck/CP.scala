package cp

object CP {
  final class NotImplementedException extends Exception

  def choose[A](pred : A => Boolean) : A = {
    throw new NotImplementedException()
  }
}
