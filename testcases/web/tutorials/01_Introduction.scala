import leon.Utils._

/**
 * Code should be contained in a single top-level object 
 */
object Introduction {

  /**
   * You can define Algebraic Data Types using abstract classes and case classes.
   */
  abstract class Tree
  case class Node(left: Tree, v: BigInt, right: Tree) extends Tree
  case object Leaf extends Tree


  /**
   * You can define functions. Functions should be purely functionnal. Note
   * that some imperative constructs such as 'var' or while loops will be handled.
   */
  def content(t: Tree): Set[BigInt] = t match {
    case Node(l, v, r) => content(l) ++ content(r) ++ Set(v)
    case Leaf => Set()
  }

  /**
   * You can specify pre-conditions to a function using the "require" construct.
   * You can use previously-defined functions in your precondition
   */
  def head(t: Tree) = {
    require(t != Leaf)

    val Node(_, v, _) = t

    v
  }


  /**
   * The following function uses head in unsafe ways:
   *
   * To verify a function, click on its name and select "verify". You can also
   * hit Alt+v while within the body of a function.
   *
   * Verify whether test1, test2 and test3 are safe.
   */

  def simpleSorted(t: Tree) = {
    require(t != Leaf)

    val Node(l, v, r) = t

    (head(l) < v) && (v < head(r))
  }

  /**
   * You can specify post-conditions using "ensuring".
   */
  def contains(what: BigInt, t: Tree): Boolean = (t match {
    case Leaf =>
      false

    case Node(l, v, r) =>
      (v == what) || contains(what, l) || contains(what, r)

  }) ensuring { res => res == (content(t) contains what) }

  /**
   * Can you spot the bug in this implementation of contains? Leon can.
   */
  def containsBuggy(what: BigInt, t: Tree): Boolean = (t match {
    case Leaf =>
      false

    case Node(l, v, r) =>
      (v == what) || contains(what, l) || contains(v, r)

  }) ensuring { res => res == (content(t) contains what) }


  /**
   * Leon can also verify the completeness of the pattern matching:
   */
  def unsafeMatch(t: Tree) = t match {
    case Node(l, v, r) if v == 0 =>
    case Leaf =>
  }

  def unsafeHead(t: Tree) = {
    val Node(_, v, _) = t   // This translates to pattern matching

    v
  }

}
