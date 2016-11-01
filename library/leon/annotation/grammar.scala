/* Copyright 2009-2016 EPFL, Lausanne */

package leon.annotation

import scala.annotation.StaticAnnotation

object grammar {

  @ignore
  class label extends StaticAnnotation

  @ignore
  class production(weight: Int = 1) extends StaticAnnotation

  @ignore
  class tag(name: String) extends StaticAnnotation
}
