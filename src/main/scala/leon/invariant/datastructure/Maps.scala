/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.datastructure

import scala.annotation.tailrec

class MultiMap[A, B] extends scala.collection.mutable.HashMap[A, scala.collection.mutable.Set[B]] with scala.collection.mutable.MultiMap[A, B] {
  /**
   * Creates a new map and does not change the existing map
   */
  def append(that: MultiMap[A, B]): MultiMap[A, B] = {
    val newmap = new MultiMap[A, B]()
    this.foreach { case (k, vset) => newmap += (k -> vset) }
    that.foreach {
      case (k, vset) => vset.foreach(v => newmap.addBinding(k, v))
    }
    newmap
  }
}

/**
 * A multimap that allows duplicate entries
 */
class OrderedMultiMap[A, B] extends scala.collection.mutable.HashMap[A, scala.collection.mutable.ListBuffer[B]] {

  def addBinding(key: A, value: B): this.type = {
    get(key) match {
      case None =>
        val list = new scala.collection.mutable.ListBuffer[B]()
        list += value
        this(key) = list
      case Some(list) =>
        list += value
    }
    this
  }

  /**
   * Creates a new map and does not change the existing map
   */
  def append(that: OrderedMultiMap[A, B]): OrderedMultiMap[A, B] = {
    val newmap = new OrderedMultiMap[A, B]()
    this.foreach { case (k, vlist) => newmap += (k -> vlist) }
    that.foreach {
      case (k, vlist) => vlist.foreach(v => newmap.addBinding(k, v))
    }
    newmap
  }

  /**
   * Make the value of every key distinct
   */
  def distinct: OrderedMultiMap[A, B] = {
    val newmap = new OrderedMultiMap[A, B]()
    this.foreach { case (k, vlist) => newmap += (k -> vlist.distinct) }
    newmap
  }
}

/**
 * Implements a mapping from Seq[A] to B where Seq[A]
 * is stored as a Trie
 */
final class TrieMap[A, B] {
  var childrenMap = Map[A, TrieMap[A, B]]()
  var dataMap = Map[A, B]()

  @tailrec def addBinding(key: Seq[A], value: B) {
    key match {
      case Seq() =>
        throw new IllegalStateException("Key is empty!!")
      case Seq(x) =>
        //add the value to the dataMap
        if (dataMap.contains(x))
          throw new IllegalStateException("A mapping for key already exists: " + x + " --> " + dataMap(x))
        else
          dataMap += (x -> value)
      case head +: tail => //here, tail has at least one element
        //check if we have an entry for seq(0) if yes go to the children, if not create one
        val child = childrenMap.getOrElse(head, {
          val ch = new TrieMap[A, B]()
          childrenMap += (head -> ch)
          ch
        })
        child.addBinding(tail, value)
    }
  }

  @tailrec def lookup(key: Seq[A]): Option[B] = {
    key match {
      case Seq() =>
        throw new IllegalStateException("Key is empty!!")
      case Seq(x) =>
        dataMap.get(x)
      case head +: tail => //here, tail has at least one element
        childrenMap.get(head) match {
          case Some(child) =>
            child.lookup(tail)
          case _ => None
        }
    }
  }
}

class CounterMap[T] extends scala.collection.mutable.HashMap[T, Int] {
  def inc(v: T) = {
    if (this.contains(v))
      this(v) += 1
    else this += (v -> 1)
  }
}