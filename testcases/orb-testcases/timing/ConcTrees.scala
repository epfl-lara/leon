package conctrees

import leon.instrumentation._
import leon.collection._
import leon.lang._
import ListSpecs._
import leon.annotation._
import leon.invariant._

object ConcTrees {

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  sealed abstract class Conc[T] {

    def isEmpty: Boolean = {
      this == Empty[T]()
    }

    def isLeaf: Boolean = {
      this match {
        case Empty() => true
        case Single(_) => true
        case _ => false
      }
    }

    def isNormalized: Boolean = this match {
      case Append(_, _) => false
      case _ => true
    }

    def valid: Boolean = {
      concInv && balanced && appendInv
    }

    /**
     * (a) left and right trees of conc node should be non-empty
     * (b) they cannot be append nodes
     */
    def concInv: Boolean = this match {
      case CC(l, r) =>
        !l.isEmpty && !r.isEmpty &&
        l.isNormalized && r.isNormalized &&
        l.concInv && r.concInv
      case _ => true
    }

    def balanced: Boolean = {
      this match {
        case CC(l, r) =>
          l.level - r.level >= -1 && l.level - r.level <= 1 &&
          l.balanced && r.balanced
        case _ => true
      }
    }

    /**
     * (a) Right subtree of an append node is not an append node
     * (b) If the tree is of the form a@Append(b@Append(_,_),_) then
     *    a.right.level < b.right.level
     * (c) left and right are not empty
     */
    def appendInv: Boolean = this match {
      case Append(l, r) =>
      !l.isEmpty && !r.isEmpty &&
      l.valid && r.valid &&
      r.isNormalized &&
      (l match {
        case Append(_, lr) =>
        lr.level > r.level
        case _ =>
        l.level > r.level
        })
      case _ => true
    }

    val level: BigInt = {
      (this match {
        case Empty() => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
        case Append(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)

    val size: BigInt = {
      (this match {
        case Empty() => 0
        case Single(x) => 1
        case CC(l, r) =>
          l.size + r.size
        case Append(l, r) =>
          l.size + r.size
      }): BigInt
    } ensuring (_ >= 0)

    def toList: List[T] = {
      this match {
        case Empty() => Nil[T]()
        case Single(x) => Cons(x, Nil[T]())
        case CC(l, r) =>
          l.toList ++ r.toList // note: left elements precede the right elements in the list
        case Append(l, r) =>
          l.toList ++ r.toList
      }
    } ensuring (res => res.size == this.size)
  }

  case class Empty[T]() extends Conc[T]
  case class Single[T](x: T) extends Conc[T]
  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]
  case class Append[T](left: Conc[T], right: Conc[T]) extends Conc[T]

  /*class Chunk(val array: Array[T], val size: Int, val k: Int) extends Leaf[T] {
    def level = 0
    override def toString = s"Chunk(${array.mkString("", ", ", "")}; $size; $k)"
    }*/

  def lookup[T](xs: Conc[T], i: BigInt): T = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    xs match {
      case Single(x) => x
      case CC(l, r) =>
        if (i < l.size) {
          lookup(l, i)
        } else {
          lookup(r, i - l.size)
        }
      case Append(l, r) =>
        if (i < l.size) {
          lookup(l, i)
        } else {
          lookup(r, i - l.size)
        }
    }
  } ensuring (res => tmpl((a,b) => time <= a*xs.level + b) && // lookup time is linear in the height
    res == xs.toList(i) && // correctness
    instAppendIndexAxiom(xs, i)) // an auxiliary axiom instantiation that is required for the proof

  // @library
  def instAppendIndexAxiom[T](xs: Conc[T], i: BigInt): Boolean = {
    require(0 <= i && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case Append(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case _ => true
    }
  }.holds

  @library
  def update[T](xs: Conc[T], i: BigInt, y: T): Conc[T] = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    xs match {
      case Single(x) => Single(y)
      case CC(l, r) =>
        if (i < l.size)
          CC(update(l, i, y), r)
        else
          CC(l, update(r, i - l.size, y))
      case Append(l, r) =>
        if (i < l.size)
          Append(update(l, i, y), r)
        else
          Append(l, update(r, i - l.size, y))
    }
  } ensuring (res => res.level == xs.level && // heights of the input and output trees are equal
   res.valid && // tree invariants are preserved
   tmpl((a,b) => time <= a*xs.level + b) && // update time is linear in the height of the tree
   res.toList == xs.toList.updated(i, y) && // correctness
   numTrees(res) == numTrees(xs) && //auxiliary property that preserves the potential function
   instAppendUpdateAxiom(xs, i, y)) // an auxiliary axiom instantiation

  @library
  def instAppendUpdateAxiom[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case Append(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  /**
  * A generic concat that applies to general concTrees
  */
  @library
  def concat[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid)
    concatNormalized(normalize(xs), normalize(ys))
  }

  /**
  * This concat applies only to normalized trees.
  * This prevents concat from being recursive
  */
  @library
  def concatNormalized[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid &&
      xs.isNormalized && ys.isNormalized)
    (xs, ys) match {
      case (xs, Empty()) => xs
      case (Empty(), ys) => ys
      case _ =>
        concatNonEmpty(xs, ys)
    }
  } ensuring (res => res.valid && // tree invariants
   res.level <= max(xs.level, ys.level) + 1 && // height invariants
   res.level >= max(xs.level, ys.level) &&
   (res.toList == xs.toList ++ ys.toList) && // correctness
   res.isNormalized //auxiliary properties
   )

  //@library
  def concatNonEmpty[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid &&
      xs.isNormalized && ys.isNormalized &&
      !xs.isEmpty && !ys.isEmpty)

    val diff = ys.level - xs.level
    if (diff >= -1 && diff <= 1)
      CC(xs, ys)
    else if (diff < -1) {
      // ys is smaller than xs
      xs match {
        case CC(l, r) =>
          if (l.level >= r.level)
            CC(l, concatNonEmpty(r, ys))
          else {
            r match {
              case CC(rl, rr) =>
                val nrr = concatNonEmpty(rr, ys)
                if (nrr.level == xs.level - 3)
                  CC(l, CC(rl, nrr))
                else
                  CC(CC(l, rl), nrr)
            }
          }
      }
    } else {
      ys match {
        case CC(l, r) =>
          if (r.level >= l.level)
            CC(concatNonEmpty(xs, l), r)
          else {
            l match {
              case CC(ll, lr) =>
                val nll = concatNonEmpty(xs, ll)
                if (nll.level == ys.level - 3)
                  CC(CC(nll, lr), r)
                else
                  CC(nll, CC(lr, r))
            }
          }
      }
    }
  } ensuring (res => tmpl((a,b) => time <= a*abs(xs.level - ys.level) + b) && // time bound
   res.level <= max(xs.level, ys.level) + 1 && // height invariants
   res.level >= max(xs.level, ys.level) &&
   res.balanced && res.appendInv && res.concInv && //this is should not be needed. But, seems necessary for leon
   res.valid && // tree invariant is preserved
   res.toList == xs.toList ++ ys.toList && // correctness
   res.isNormalized && // auxiliary properties
   appendAssocInst(xs, ys) // instantiation of an axiom
   )

  @library
  def appendAssocInst[T](xs: Conc[T], ys: Conc[T]): Boolean = {
    (xs match {
      case CC(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList) && //instantiation of associativity of concatenation
        (r match {
          case CC(rl, rr) =>
            appendAssoc(rl.toList, rr.toList, ys.toList) &&
            appendAssoc(l.toList, rl.toList, rr.toList ++ ys.toList)
          case _ => true
        })
      case _ => true
    }) &&
    (ys match {
      case CC(l, r) =>
        appendAssoc(xs.toList, l.toList, r.toList) &&
        (l match {
          case CC(ll, lr) =>
            appendAssoc(xs.toList, ll.toList, lr.toList) &&
            appendAssoc(xs.toList ++ ll.toList, lr.toList, r.toList)
          case _ => true
        })
      case _ => true
    })
  }.holds

   @library
  def insert[T](xs: Conc[T], i: BigInt, y: T): Conc[T] = {
    require(xs.valid && i >= 0 && i <= xs.size &&
      xs.isNormalized) //note the precondition
    xs match {
      case Empty() => Single(y)
      case Single(x) =>
        if (i == 0)
          CC(Single(y), xs)
        else
          CC(xs, Single(y))
      case CC(l, r) if i < l.size =>
        concatNonEmpty(insert(l, i, y), r)
      case CC(l, r) =>
        concatNonEmpty(l, insert(r, i - l.size, y))
    }
  } ensuring (res => res.valid && res.isNormalized && // tree invariants
   res.level - xs.level <= 1 && res.level >= xs.level && // height of the output tree is at most 1 greater than that of the input tree
   tmpl((a,b) => time <= a*xs.level + b) && // time is linear in the height of the tree
   res.toList == xs.toList.insertAt(i, y) && // correctness
   insertAppendAxiomInst(xs, i, y) // instantiation of an axiom
   )

  @library
  def insertAppendAxiomInst[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i <= xs.size)
    xs match {
      case CC(l, r) => appendInsert(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  //TODO: why with instrumentation we are not able prove the running time here ? (performance bug ?)
  @library
  def split[T](xs: Conc[T], n: BigInt): (Conc[T], Conc[T]) = {
    require(xs.valid && xs.isNormalized)
    xs match {
      case Empty() =>
        (Empty(), Empty())
      case s @ Single(x) =>
        if (n <= 0) { //a minor fix
          (Empty(), s)
        } else {
          (s, Empty())
        }
      case CC(l, r) =>
        if (n < l.size) {
          val (ll, lr) = split(l, n)
          (ll, concatNormalized(lr, r))
        } else if (n > l.size) {
            val (rl, rr) = split(r, n - l.size)
            (concatNormalized(l, rl), rr)
        } else {
          (l, r)
        }
    }
  } ensuring (res => res._1.valid && res._2.valid && // tree invariants are preserved
   res._1.isNormalized && res._2.isNormalized &&
   xs.level >= res._1.level && xs.level >= res._2.level && // height bounds of the resulting tree
   tmpl((a,b,c,d) => time <= a*xs.level + b*res._1.level + c*res._2.level + d) && // time is linear in height
   res._1.toList == xs.toList.take(n) && res._2.toList == xs.toList.drop(n) && // correctness
   instSplitAxiom(xs, n) // instantiation of an axiom
   )

  @library
  def instSplitAxiom[T](xs: Conc[T], n: BigInt): Boolean = {
    xs match {
      case CC(l, r) =>
        appendTakeDrop(l.toList, r.toList, n)
      case _ => true
    }
  }.holds

   @library
  def append[T](xs: Conc[T], x: T): Conc[T] = {
    require(xs.valid)
    val ys = Single[T](x)
    xs match {
      case xs @ Append(_, _) =>
        appendPriv(xs, ys)
      case CC(_, _) =>
        Append(xs, ys) //creating an append node
      case Empty() =>
        ys
      case Single(_) =>
        CC(xs, ys)
    }
  } ensuring (res => res.valid && //conctree invariants
   res.toList == xs.toList ++ Cons(x, Nil[T]()) && //correctness
   res.level <= xs.level + 1 &&
   tmpl((a,b,c) => time <= a*numTrees(xs) - b*numTrees(res) + c) //time bound (worst case)
   )

  /**
  * This is a private method and is not exposed to the
  * clients of conc trees
  */
  @library
  def appendPriv[T](xs: Append[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid &&
      !ys.isEmpty && ys.isNormalized &&
      xs.right.level >= ys.level)

   if (xs.right.level > ys.level)
     Append(xs, ys)
   else {
      val zs = CC(xs.right, ys)
      xs.left match {
        case l @ Append(_, _) =>
          appendPriv(l, zs)
        case l if l.level <= zs.level => //note: here < is not possible
          CC(l, zs)
        case l =>
          Append(l, zs)
      }
    }
  } ensuring (res => res.valid && //conc tree invariants
   res.toList == xs.toList ++ ys.toList && //correctness invariants
   res.level <= xs.level + 1 &&
   tmpl((a,b,c) => time <= a*numTrees(xs) - b*numTrees(res) + c) && //time bound (worst case)
   appendAssocInst2(xs, ys))

  @library
  def appendAssocInst2[T](xs: Conc[T], ys: Conc[T]): Boolean = {
    xs match {
      case CC(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList)
      case Append(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList)
      case _ => true
    }
  }.holds

   @library
  def numTrees[T](t: Conc[T]): BigInt = {
    t match {
      case Append(l, r) => numTrees(l) + 1
      case _ => BigInt(1)
    }
  } ensuring (res => res >= 0)

  @library
  def normalize[T](t: Conc[T]): Conc[T] = {
    require(t.valid)
    t match {
      case Append(l @ Append(_, _), r) =>
        wrap(l, r)
      case Append(l, r) =>
        concatNormalized(l, r)
      case _ => t
    }
  } ensuring (res => res.valid &&
    res.isNormalized &&
    res.toList == t.toList && //correctness
    res.size == t.size && res.level <= t.level && //normalize preserves level and size
    tmpl((a,b) => time <= a*t.level + b) //time bound (a little over approximate)
    )

       @library
       def wrap[T](xs: Append[T], ys: Conc[T]): Conc[T] = {
         require(xs.valid && ys.valid && ys.isNormalized &&
           xs.right.level >= ys.level)
         val nr = concatNormalized(xs.right, ys)
         xs.left match {
           case l @ Append(_, _) =>
           wrap(l, nr)
           case l =>
           concatNormalized(l, nr)
         }
         } ensuring (res => res.valid &&
           res.isNormalized &&
   res.toList == xs.toList ++ ys.toList && //correctness
   res.size == xs.size + ys.size && //other auxiliary properties
   res.level <= xs.level &&
   tmpl((a,b,c) => time <= a*xs.level - b*ys.level + c) && //time bound
   appendAssocInst2(xs, ys)) //some lemma instantiations

  /**
  * A class that represents an operation on a concTree.
  * opid - an integer that denotes the function that has to be performed e.g. append, insert, update ...
  *     opid <= 0 => the operation is lookup
  *       opid == 1 => the operation is update
  *       opid == 2 => the operation is insert
  *       opid == 3 => the operation is split
  *        opid >= 4 => the operation is append
  * index, x - denote the arguments the function given by opid
  */
  case class Operation[T](opid: BigInt, /*argument to the operations*/ index: BigInt /*for lookup, update, insert, split*/ ,
   x: T /*for update, insert, append*/ )

  /**
  * Proving amortized running time of 'Append' when used ephimerally.
  * ops- a arbitrary sequence of operations,
  * noaps - number of append operations in the list
  */
  def performOperations[T](xs: Conc[T], ops: List[Operation[T]], noaps: BigInt): Conc[T] = {
    require(xs.valid && noaps >= 0)
    ops match {
      case Cons(Operation(id, i, _), tail) if id <= 0 =>
        //we need to perform a lookup operation, but do the operation only if
        //preconditions hold
        // val _ = if (0 <= i && i < xs.size)
        //     lookup(xs, i)
        //   else BigInt(0)
            performOperations(xs, tail, noaps) //returns the time taken by appends in the remaining operations

      case Cons(Operation(id, i, x), tail) if id == 1 =>
        val newt = if (0 <= i && i < xs.size)
            update(xs, i, x)
          else xs
            //note that only the return value is used by the subsequent operations (emphimeral use)
            performOperations(newt, tail, noaps)

      case Cons(Operation(id, i, x), tail) if id == 2 =>
        val newt = if (0 <= i && i <= xs.size)
            insert(normalize(xs), i, x)
          else xs
            performOperations(newt, tail, noaps)

      case Cons(Operation(id, n, _), tail) if id == 3 =>
        //use the larger tree to perform the remaining operations
        val (newl, newr) = split(normalize(xs), n)
        val newt = if (newl.size >= newr.size) newl else newr
        performOperations(newt, tail, noaps)

      case Cons(Operation(id, _, x), tail) if noaps > 0 =>
        //here, we need to perform append operation
        val newt = append(xs, x)
        val r = performOperations(newt, tail, noaps - 1)
        r //time taken by this append and those that follow it

      case _ =>
        xs
    }
  } ensuring (res => tmpl((a, b) => time <= a*noaps + b*numTrees(xs)))
//res._2 <= noaps + 2*nops*(xs.level + res._1.level)+ numTrees(xs)
}
