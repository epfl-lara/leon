import leon.invariant._

object AmortizedQueue {
  def concat(l1: BigInt, l2: BigInt): BigInt = {
    require(l1 >= 0 && l2 >= 0)
    if (l1 == 0)
      BigInt(3)
    else
      concat(l1 - 1, l2 + 1) + 5
  } ensuring (res => tmpl((a, b) => res <= a * l1 + b))

  def reverseRec(l1: BigInt, l2: BigInt): BigInt = {
    require(l1 >= 0 && l2 >= 0)
    if (l1 == 0)
      BigInt(3)
    else {
      reverseRec(l1 - 1, l2 + 1) + 6
    }
  } ensuring (res => tmpl((a, b) => res <= a * l1 + b))

  def reverse(l: BigInt): BigInt = {
    require(l >= 0)
    reverseRec(l, 0) + 1
  } ensuring (res => tmpl((a, b) => res <= a * l + b))

  def create(front: BigInt, rear: BigInt): BigInt = {
    require(front >= 0 && rear >= 0)
    if (rear <= front)
      BigInt(4)
    else {
      val t1 = reverse(rear)
      val t2 = concat(front, rear)
      t1 + t2 + 7
    }
  }

  def enqueue(q: BigInt, front: BigInt, rear: BigInt): BigInt = {
    require(q == front + rear && q >= 0 && front >= 0 && rear >= 0)
    create(front, rear) + 5
  } ensuring (res => tmpl((a, b) => res <= a * q + b))

  def dequeue(q: BigInt, front: BigInt, rear: BigInt): BigInt = {
    require(q == front + rear && q >= 1 && front >= rear && rear >= 0)
    if (front >= 1) {
      create(front - 1, rear) + 4
    } else {
      //since front should be greater than rear, here rear should be 0 as well
      BigInt(5)
    }
  } ensuring (res => tmpl((a, b) => res <= a * q + b))

  def removeLast(l: BigInt): BigInt = {
    require(l >= 1)
    if (l == 1) {
      BigInt(4)
    } else {
      removeLast(l - 1) + 6
    }
  } ensuring (res => tmpl((a, b) => res <= a * l + b))

  def pop(q: BigInt, front: BigInt, rear: BigInt): BigInt = {
    require(q == front + rear && q >= 1 && front >= rear && rear >= 0)
    if (rear >= 1) {
      BigInt(3)
    } else {
      val t1 = removeLast(front)
      t1 + 5
    }
  } ensuring (res => tmpl((a, b) => res <= a * q + b))
}
