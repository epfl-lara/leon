import leon.annotation._
import leon.collection._
import leon.lang._

object Unapply {

  @isabelle.proof(method = """(cases "<var xs>", auto)""")
  def check[A](xs: List[A]) = {
    xs match {
      case Nil() => true
      case _ :: _ => true
    }
  }.holds

}
