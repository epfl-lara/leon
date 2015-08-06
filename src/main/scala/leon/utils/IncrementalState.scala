package leon.utils

trait IncrementalState {
  def push(): Unit
  def pop(): Unit

  def clear(): Unit
  def reset(): Unit
}
