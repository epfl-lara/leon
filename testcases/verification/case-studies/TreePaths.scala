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

  def inside(t: Tree, subtree: Tree): Boolean = {
    if (t==subtree) true
    else {
      t match {
        case Empty => false
        case Node(left,_,right) => inside(left, subtree) || inside(right, subtree)
      }
    }
  }
  
  def lookup(t: Tree, path : List[Dir]): Option[Tree] = {
    (t,path) match {
      case (_,Nil()) => Some[Tree](t)
      case (Empty,_) => None[Tree]()
      case (Node(left,_,_),  Cons(Left,rest)) => lookup(left,rest)
      case (Node(_,_,right), Cons(Right,rest)) => lookup(right,rest)
    }
  }

  def nil[A]: List[A] = Nil[A]
  def cons[A](x: A, lst: List[A]): List[A] = Cons[A](x,lst)
  def some[A](x: A): Option[A] = Some[A](x)

  // Function find1 has a counterexample.
  def find1(t: Tree, subtree: Tree): Option[List[Dir]] = ({
    if (t==subtree) some(nil[Dir])
    else {
      t match {
        case Empty => None[List[Dir]]
        case Node(left,_,right) => {
          find1(left,subtree) match {
            case None() => find1(right,subtree)
            case v => v
          }
        }
      }
    }
  }: Option[List[Dir]]).ensuring((res:Option[List[Dir]]) => (res match {
    case None() => !inside(t, subtree)
    case Some(path) => lookup(t, path)==Some(subtree)
  }))

  // Function find is correct
  def find(t: Tree, subtree: Tree): Option[List[Dir]] = ({
    if (t==subtree) some(nil[Dir])
    else {
      t match {
        case Empty => None[List[Dir]]
        case Node(left,_,right) => {
          find(left,subtree) match {
            case None() => { find(right,subtree) match {
              case None() => None()
              case Some(path) => Some(cons(Right,path))
            }}
            case Some(path) => Some(cons(Left, path))
          }
        }
      }
    }
  }: Option[List[Dir]]).ensuring((res:Option[List[Dir]]) => (res match {
    case None() => !inside(t, subtree)
    case Some(path) => lookup(t, path)==Some(subtree)
  }))

  def replace(t: Tree, path: List[Dir], newT: Tree): Tree = {
    require(lookup(t, path) != None[Tree]())
    (t,path) match {
      case (_,Nil()) => newT
      case (Node(left,v,right), Cons(Left, rest)) => Node(replace(left,rest, newT), v, right)
      case (Node(left,v,right), Cons(Right,rest)) => Node(left, v, replace(right, rest, newT))
    }
  } ensuring(res => lookup(res, path)==Some(newT))

}
