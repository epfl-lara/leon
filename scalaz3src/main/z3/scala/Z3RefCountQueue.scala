package z3.scala

import z3.{Z3Wrapper,Pointer}

class Z3RefCountQueue[T <: Z3Object](maxSize: Int = 512) {
  private val drQueue = collection.mutable.Queue[T]()

  protected[z3] def incRef(t: T) {
    t.incRef()

    if (drQueue.size > maxSize) {
      clearQueue()
    }
  }

  protected[z3] def decRef(t: T) {
    synchronized {
      drQueue += t
    }
  }

  protected[z3] def clearQueue() {
    synchronized {
      for (t <- drQueue) {
        t.decRef()
      }
      drQueue.clear()
    }
  }
}
