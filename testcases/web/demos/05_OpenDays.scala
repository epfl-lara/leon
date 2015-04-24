import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object EpflOpenDays {

  sealed abstract class Liste
  case object Vide extends Liste
  case class Elem(e: BigInt, reste: Liste) extends Liste

  def taille(l: Liste): BigInt = (l match {
      case Vide => 0
      case Elem(x, reste) => x + taille(reste)
  })
  
  //def s0 = taille(Elem(10, Elem(1000, Vide)))
  
  //ensuring(res => res >= 0)

  //def s1 = taille(Elem(10, Elem(1000, Vide)))

  def contenu(l: Liste): Set[BigInt] = l match {
    case Vide => Set()
    case Elem(e, reste) => Set(e) ++ contenu(reste)
  }

/*
  def estTriée(l: Liste): Boolean = l match {
    case Vide                      => true
    case Elem(_, Vide)             => true
    case Elem(e1, Elem(e2, reste)) => 
      e1 < e2 && estTriée(Elem(e2, reste))
  }
*/

  //def t1 = estTriée(Elem(10, Elem(14, Elem(20, Elem(25, Vide)))))
  //def t2 = estTriée(Elem(10, Elem(14, Elem(1, Elem(2, Vide)))))

/*
  def insertion(x: BigInt, l: Liste): Liste = {
    require(estTriée(l))
    l match {
      case Vide                       => Elem(x, Vide)
      case Elem(e, reste) if (x == e) => l
      case Elem(e, reste) if (x < e)  => Elem(x, Elem(e,reste))
      case Elem(e, reste) if (x > e)  => Elem(e, insertion(x, reste))
    }
  } ensuring { (res: Liste) => 
     estTriée(res) && 
     contenu(res) == contenu(l) ++ Set(x)
  }
*/
/*
  def insertionMagique(x: BigInt, l: Liste): Liste = {
    require(estTriée(l))
    choose { (res: Liste) =>
      estTriée(res) &&
      contenu(res) == contenu(l) ++ Set(x)
    }
  }
*/

  //def m1 = insertionMagique(17, Elem(10, Elem(14, Elem(20, Elem(25, Vide)))))

/*
  def trier(l: Liste) = choose{ (res: Liste) => 
    estTriée(res) && contenu(res) == contenu(l)
  }
*/

  //def mm = trier(Elem(10, Elem(14, Elem(1, Elem(2, Vide)))))

}

