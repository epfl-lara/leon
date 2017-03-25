/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang

import java.lang.RuntimeException
import leon.annotation._
import scala.Boolean

package object xlang {
  @ignore
  def epsilon[A](pred: (A) => Boolean): A = throw new RuntimeException("Implementation not supported")
}
