/**
 * In this exercise, you will have to implement a packed representation of a set of numbers.
 * This representation uses a chained list of sorted ranges to represent the stored values.
 * 
 *   [0, 10] :: [15, 15] :: Empty 
 * 
 * stores
 * 
 *   Set(0,1,2,3,4,5,6,7,8,9,10,15)
 * 
 * You need to implement + and - that adds and deletes single elements from the set.
 * Leon will not generally be able to verify everything, but it should give you 
 * counter-examples in case you do something wrong.
 */
 
import leon.lang._
import leon.lang.synthesis._
import leon.annotation._
 
object PackedSet {
  case class Range(min: BigInt, max: BigInt) {
    def size: BigInt = {
      if (max >= min) max-min+1
      else 0
    }
 
    def content: Set[BigInt] = {
      if (max == min) Set(min)
      else if (max > min) Set(min) ++ Range(min+1, max).content
      else Set()
    }
 
    def contains(v: BigInt): Boolean = {
      min <= v && max >= v
    }
 
    def <(that: Range) = {
      this.min < that.min
    }
 
    def merge(that: Range): Range = {
      require(this.min == that.min)
      Range(min, if (this.max > that.max) this.max else that.max)
    } ensuring {
      res => res.content == this.content ++ that.content
    }
  }
 
 
  abstract class PackedSet {
    def size: BigInt = {
      this match {
        case Empty => 0
        case NonEmpty(r, t) => r.size + t.size
      }
    }
 
    def depth: BigInt = {
      this match {
        case Empty => 0
        case NonEmpty(_, t) => 1 + t.depth
      }
    }
 
    def content: Set[BigInt] = {
      this match {
        case Empty => Set()
        case NonEmpty(r, t) => r.content ++ t.content
      }
    }
 
    def contains(v: BigInt): Boolean = {
      this match {
        case Empty => false
        case NonEmpty(r, t) => 
          if (r.min > v) false
          else r.contains(v) || t.contains(v)
      } 
    }
 
    def isPackedSet = isSorted && isPacked
 
    def isSorted: Boolean = {
      this match {
        case NonEmpty(r1, t @ NonEmpty(r2, _)) => r1 < r2  && t.isSorted
        case _ => true
      }
    }
 
    def isPacked: Boolean = {
      this match {
        case Empty => true
        case NonEmpty(r, t) => r.size >= 1 && t.isPacked
      }
    }
 
    def +(v: BigInt): PackedSet = {
      require(this.isPackedSet)
      this // TODO
    } ensuring {
      res => res.content == this.content ++ Set(v) &&
             res.isPackedSet
    }
 
    def -(v: BigInt): PackedSet = {
      require(this.isPackedSet)
      this // TODO
    } ensuring {
      res => res.content == this.content -- Set(v) &&
             res.isPackedSet
    }
 
  }
  case class NonEmpty(r: Range, tail: PackedSet) extends PackedSet
  case object Empty extends PackedSet
 
 
}
