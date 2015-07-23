import leon.lang._
import leon.collection._
import leon.annotation._
object Tree { 
  sealed abstract class Tree
  case object Empty extends Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree

  sealed abstract class Dir
  case object Left extends Dir
  case object Right extends Dir

  def nil[A]: List[A] = Nil[A]
  def cons[A](x: A, lst: List[A]): List[A] = Cons[A](x,lst)
  def some[A](x: A): Option[A] = Some[A](x)
  def none[A]: Option[A] = None[A]

  case class Path(p: List[Dir])
  def pnil = Path(nil)

  def inside(t: Tree, subtree: Tree): Boolean = {
    if (t==subtree) true
    else {
      t match {
        case Empty => false
        case Node(left,_,right) => inside(left, subtree) || inside(right, subtree)
      }
    }
  }
  
  def lookup(t: Tree, path : Path): Option[Tree] = {
    (t,path.p) match {
      case (_,Nil()) => some(t)
      case (Empty,_) => none
      case (Node(left,_,_),  Cons(Left,rest)) => lookup(left,Path(rest))
      case (Node(_,_,right), Cons(Right,rest)) => lookup(right,Path(rest))
    }
  }

  // Function find1 has a counterexample.
  def find1(t: Tree, subtree: Tree): Option[Path] = ({
    if (t==subtree) some(pnil)
    else {
      t match {
        case Empty => none
        case Node(left,_,right) => {
          find1(left,subtree) match {
            case None() => find1(right,subtree)
            case v => v
          }
        }
      }
    }
  }: Option[Path]).ensuring(res => (res match {
    case None() => !inside(t, subtree)
    case Some(path) => lookup(t, path)==Some(subtree)
  }))

  // Function find is correct
  def find(t: Tree, subtree: Tree): Option[Path] = ({
    if (t==subtree) some(pnil)
    else {
      t match {
        case Empty => none
        case Node(left,_,right) => {
          find(left,subtree) match {
            case None() => { find(right,subtree) match {
              case None() => None()
              case Some(Path(p)) => Some(Path(cons(Right,p)))
            }}
            case Some(Path(p)) => Some(Path(cons(Left, p)))
          }
        }
      }
    }
  }: Option[Path]).ensuring(res => (res match {
    case None() => !inside(t, subtree)
    case Some(path) => lookup(t, path)==Some(subtree)
  }))

  def replace(t: Tree, path: Path, newT: Tree): Tree = {
    require(lookup(t, path) != none[Tree])
    (t,path.p) match {
      case (_,Nil()) => newT
      case (Node(left,v,right), Cons(Left, rest)) => Node(replace(left,Path(rest), newT), v, right)
      case (Node(left,v,right), Cons(Right,rest)) => Node(left, v, replace(right, Path(rest), newT))
    }
  } ensuring(res => lookup(res, path)==some(newT))

  case class Flat(trees: List[(Path, Tree)])
  def fnil = Flat(nil)

  def subtrees(t: Tree): Flat = {
    t match {
      case Empty => fnil
      case Node(left,v,right) => 
        Flat(addLeft(subtrees(left)).trees ++ ((pnil,t) :: addRight(subtrees(right)).trees))
    }
  }

  def addLeft(f: Flat): Flat = {
    f.trees match {
      case Nil() => fnil
      case (p,t) :: trees1 => Flat((Path(Left::p.p),t) :: addLeft(Flat(trees1)).trees)
    }
  }
  def addRight(f: Flat): Flat = {
    f.trees match {
      case Nil() => fnil
      case (p,t) :: trees1 => Flat((Path(Right::p.p),t) :: addRight(Flat(trees1)).trees)
    }
  }
}
