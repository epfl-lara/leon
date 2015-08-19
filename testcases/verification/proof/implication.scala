package test

import leon.lang._
import leon.proof._

object ImplicationExample {
    /*
     * Some implication example.
     *
     * This example actually is based on incorrect premises but
     * the proof in itself should correct.
     */

    sealed abstract class Animal
    case class Insect() extends Animal
    case class Mamal() extends Animal

    sealed abstract class AnimalKind
    case object InsectKind extends AnimalKind
    case object MamalKind extends AnimalKind

    sealed abstract class LegsProperty
    case object HasEigthLegs extends LegsProperty
    //case object HasTwoLegs extends LegsProperty

    sealed abstract class PlayerKind
    case object PockerKind extends PlayerKind
    //

    val jeff = Insect()

    def isEqual(a: Animal, b: Animal): Boolean = a == b

    def isKindOf(a: Animal, k: AnimalKind): Boolean = a match {
        case Insect() => k == InsectKind
        case Mamal()  => k == MamalKind
    }

    def hasLegsProperty(k: AnimalKind, l: LegsProperty): Boolean = k match {
        case InsectKind => l == HasEigthLegs
        case MamalKind  => l != HasEigthLegs
    }

    def isKindOf(l: LegsProperty, p: PlayerKind): Boolean = l match {
        case HasEigthLegs => p == PockerKind
    }

    def implies(a: Boolean, b: Boolean) = a ==> b

    // Jeff plays Poker
    def lemma(animal: Animal): Boolean = {
        isEqual(animal, jeff) ==>
        isKindOf(jeff, InsectKind) ==>
        hasLegsProperty(InsectKind, HasEigthLegs) ==>
        isKindOf(HasEigthLegs, PockerKind)
    }.holds

}

