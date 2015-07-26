import leon.lang._
import leon.lang.synthesis._
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

  case class Path(p: List[Dir]) extends AnyVal
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

  def valid(t: Tree, path: Path): Boolean = {
    lookup(t, path) != none[Tree]
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
    require(valid(t,path))
    (t,path.p) match {
      case (_,Nil()) => newT
      case (Node(left,v,right), Cons(Left, rest)) => Node(replace(left,Path(rest), newT), v, right)
      case (Node(left,v,right), Cons(Right,rest)) => Node(left, v, replace(right, Path(rest), newT))
    }
  } ensuring(res => lookup(res, path)==some(newT))

  /* This has a counterexample, e.g. 
   path  -> Path(Cons[Dir](Left, Cons[Dir](Left, Nil[Dir]())))
   path1 -> Path(Nil[Dir]())
   t     -> Empty
   */
  def replaceKeepsLemmaInvalid1(t: Tree, path: Path, newT: Tree, path1: Path): Boolean = {
    require(path != path1)
    lookup(replace(t, path, newT), path1)==lookup(t, path1)
  }

  def prefix(p1: Path, p2: Path): Boolean = {
    (p1.p, p2.p) match {
      case (Nil(),_) => true
      case (h1 :: r1, h2 :: r2) => {
        (h1==h2) && prefix(Path(r1), Path(r2))
      }
    }
  }

  def replaceKeepsLemmaInvalid2(t: Tree, path: Path, newT: Tree, path1: Path): Boolean = {
    require(!prefix(path1, path))
    lookup(replace(t, path, newT), path1)==lookup(t, path1)
  }.holds

  //@induct
  def replaceKeepsLemma(t: Tree, path: Path, newT: Tree, path1: Path): Boolean = {
    require(valid(t, path) && !prefix(path, path1))
    lookup(replace(t, path, newT), path1)==lookup(t, path1)
  }.holds

  case class Flat(trees: List[(Path, Tree)]) extends AnyVal

  def fnil = Flat(nil[(Path,Tree)])

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

  def unflat(f: Flat) : Option[Tree] = {
    // TO IMPLEMENT
    ???[Option[Tree]]
  } ensuring(res => res match {
    case None() => true
    case Some(t) => equiv(subtrees(t), f)
  })

  def equiv(f1: Flat, f2: Flat): Boolean = {
    f1.trees.content == f2.trees.content
  }

/*
  def unsomep(po: Option[Path]): Path = {
    require()
  }

  def diff(t1: Tree, t2: Tree): Option[Path] = {
    (t1, t2) match {
      case (Empty, Empty) => none
      case (Empty,Node(_,_,_)) => some(pnil)
      case (Node(_,_,_),Empty) => some(pnil)
      case (Node(l1,v1,r1),Node(l2,v2,r2)) => {
        if (v1 != v2) some(pnil)
        else if (l1==l2) Path(cons(Right,diff(r1,r2).p))
        else if (r1==r2) Path(cons(Left, diff(l1,l2).p))
      }
    }
  }
 */
}
