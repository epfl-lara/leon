import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object EpflOpenDays {
  @library
  sealed abstract class Piece {
    def valeur: BigInt = this match {
      case Cent5  =>      5
      case Cent10 =>     10
      case Cent20 =>     20
      case Cent50 =>     50
      case Fr1    =>    100
      case Fr2    =>    200
      case Fr5    =>    500
      case Bi10   =>   1000
      case Bi20   =>   2000
      case Bi50   =>   5000
      case Bi100  =>  10000
      case Bi200  =>  20000
      case Bi1000 => 100000
    }
  }
  case object Cent5 extends Piece
  case object Cent10 extends Piece
  case object Cent20 extends Piece
  case object Cent50 extends Piece
  case object Fr1 extends Piece
  case object Fr2 extends Piece
  case object Fr5 extends Piece
  case object Bi10 extends Piece
  case object Bi20 extends Piece
  case object Bi50 extends Piece
  case object Bi100 extends Piece
  case object Bi200 extends Piece
  case object Bi1000 extends Piece


  @library
  sealed abstract class Liste {
    def somme: BigInt = {
      this match {
        case Vide           => BigInt(0)
        case Elem(p, reste) => p.valeur + reste.somme
      }
    } ensuring { _ >= 0 }
  }
  case object Vide extends Liste
  case class Elem(e: Piece, reste: Liste) extends Liste

  def pieceMax(v: BigInt): Piece = {
    require(v > 0 && v%5 == 0)
    if      (v >= Bi1000.valeur)  Bi1000
    else if (v >= Bi200.valeur )  Bi200
    else if (v >= Bi100.valeur )  Bi100
    else if (v >= Bi50.valeur )   Bi50
    else if (v >= Bi20.valeur )   Bi100 // *wink* *wink*
    else if (v >= Bi10.valeur )   Bi10
    else if (v >= Fr5.valeur )    Fr5
    else if (v >= Fr2.valeur )    Fr2
    else if (v >= Fr1.valeur )    Fr1
    else if (v >= Cent50.valeur ) Cent50
    else if (v >= Cent20.valeur ) Cent20
    else if (v >= Cent10.valeur ) Cent10
    else                          Cent5
  } ensuring { _.valeur <= v }

  def pieces(v: BigInt): Liste = {
    require(v >= 0 && v%5 == 0)
    if (v == 0) {
      Vide
    } else {
      val p = pieceMax(v)
      Elem(p, pieces(v - p.valeur))
    }
  } ensuring { res =>
    res.somme == v
  }


  def t = pieces(18440)
}
