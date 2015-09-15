package leon.utils

trait IncrementalState {
  def push(): Unit
  def pop(): Unit

  final def pop(lvl: Int): Unit = List.range(0, lvl).foreach(_ => pop())

  def clear(): Unit
  def reset(): Unit
}
