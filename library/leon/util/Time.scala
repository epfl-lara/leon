/* Copyright 2009-2017 EPFL, Lausanne */

package leon.util

import leon.annotation._

/*
 * Represent a point in time, from an arbitrary epoch that is consistent for the
 * execution of the program.
 *
 * See TimePoint.now() and TimePoint.elapsedMillis().
 */
@cCode.typedef("clock_t", "time.h")
case class TimePoint private (private val point: Int)

@library
object TimePoint {
  /*
   * Get the current time.
   */
  @extern
  @cCode.function(code =
    """
    |TimePoint __FUNCTION__(void) {
    |  return clock();
    |}
    """
  )
  def now(): TimePoint = new TimePoint((System.nanoTime() / 1E06).toInt)

  /*
   * Compute the difference between two points in time, expressed in milliseconds.
   *
   * NOTE The precision of the result is not guaranteed to be in milliseconds on all platforms.
   */
  @cCode.function(code =
    """
    |int32_t __FUNCTION__(TimePoint first, TimePoint second) {
    |  return 1000 * (second - first) / CLOCKS_PER_SEC; // mind the order of operations!
    |}
    """
  )
  def elapsedMillis(first: TimePoint, second: TimePoint): Int = second.point - first.point
}

