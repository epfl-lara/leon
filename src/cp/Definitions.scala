package cp

object Definitions {
  class spec extends StaticAnnotation

  final class NotImplementedException extends Exception

  final class UnsatisfiableConstraintException extends Exception
  final class UnknownConstraintException extends Exception

  def choose[A](pred : A => Boolean) : A = {
    throw new NotImplementedException()
  }

  def choose[A,B](pred : (A,B) => Boolean) : (A,B) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C](pred : (A,B,C) => Boolean) : (A,B,C) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D](pred : (A,B,C,D) => Boolean) : (A,B,C,D) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E](pred : (A,B,C,D,E) => Boolean) : (A,B,C,D,E) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F](pred : (A,B,C,D,E,F) => Boolean) : (A,B,C,D,E,F) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G](pred : (A,B,C,D,E,F,G) => Boolean) : (A,B,C,D,E,F,G) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G,H](pred : (A,B,C,D,E,F,G,H) => Boolean) : (A,B,C,D,E,F,G,H) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G,H,I](pred : (A,B,C,D,E,F,G,H,I) => Boolean) : (A,B,C,D,E,F,G,H,I) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G,H,I,J](pred : (A,B,C,D,E,F,G,H,I,J) => Boolean) : (A,B,C,D,E,F,G,H,I,J) = {
    throw new NotImplementedException()
  }

  def find[A](pred : A => Boolean) : Option[A] = {
    throw new NotImplementedException()
  }

  def find[A,B](pred : (A,B) => Boolean) : Option[(A,B)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C](pred : (A,B,C) => Boolean) : Option[(A,B,C)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D](pred : (A,B,C,D) => Boolean) : Option[(A,B,C,D)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E](pred : (A,B,C,D,E) => Boolean) : Option[(A,B,C,D,E)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F](pred : (A,B,C,D,E,F) => Boolean) : Option[(A,B,C,D,E,F)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G](pred : (A,B,C,D,E,F,G) => Boolean) : Option[(A,B,C,D,E,F,G)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G,H](pred : (A,B,C,D,E,F,G,H) => Boolean) : Option[(A,B,C,D,E,F,G,H)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G,H,I](pred : (A,B,C,D,E,F,G,H,I) => Boolean) : Option[(A,B,C,D,E,F,G,H,I)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G,H,I,J](pred : (A,B,C,D,E,F,G,H,I,J) => Boolean) : Option[(A,B,C,D,E,F,G,H,I,J)] = {
    throw new NotImplementedException()
  }

  def findAll[A](pred : A => Boolean) : Iterator[A] = {
    throw new NotImplementedException()
  }

  def findAll[A,B](pred : (A,B) => Boolean) : Iterator[(A,B)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C](pred : (A,B,C) => Boolean) : Iterator[(A,B,C)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D](pred : (A,B,C,D) => Boolean) : Iterator[(A,B,C,D)] = {
    throw new NotImplementedException()
  }

}
