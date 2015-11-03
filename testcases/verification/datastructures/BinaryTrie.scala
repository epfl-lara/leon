/* Copyright 2009-2015 EPFL, Lausanne
 *
 * Author: Ravi
 * Date: 20.11.2013
 **/

import leon.lang._

object BinaryTrie {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(nvalue: Int, left : Tree, right: Tree) extends Tree

  sealed abstract class IList
  case class Cons(head: Int, tail: IList) extends IList
  case class Nil() extends IList

  def listSize(l: IList): Int = (l match {
    case Nil() => 0
    case Cons(x, xs) => 1 + listSize(xs)
  }) ensuring(_ >= 0)

  def height(t: Tree): Int = {
      t match{
        case Leaf() => 0
        case Node(x,l,r) => {
          val hl = height(l)
          val hr = height(r)
          if(hl > hr) hl + 1 else hr + 1
        }
      }
  } ensuring(_ >= 0)

  def insert(inp: IList, t: Tree): Tree = {
    t match {
        case Leaf() => {
          inp match {
            case Nil() => t
            case Cons(x ,xs) => {
              val newch = insert(xs, Leaf())
              newch match {
                case Leaf() => Node(x, Leaf(), Leaf())
                case Node(y, _, _) => if(y > 0) Node(x, newch, Leaf()) else Node(y, Leaf(), newch)
              }
            }
          }
        }
        case Node(v, l, r) => {
          inp match {
            case Nil() => t
            case Cons(x, Nil()) => t
            case Cons(x ,xs@Cons(y, _)) => {
              val ch = if(y > 0) l else r
              if(y > 0)
                  Node(v, insert(xs, ch), r)
              else
                Node(v, l, insert(xs, ch))
            }
            case _ => t
        }
      }
    }
  } ensuring(res => height(res) + height(t) >= listSize(inp))

  def create(inp: IList) : Tree = {
    insert(inp, Leaf())
  }ensuring(res => height(res) >= listSize(inp))
}
