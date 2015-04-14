/* Copyright 2009-2015 EPFL, Lausanne */

package leon.lang

import leon.annotation._
import scala.language.implicitConversions

package object string {
  @ignore
  implicit def strToStr(s: java.lang.String): leon.lang.string.String = {
    String(leon.collection.Nil())
  }
}
