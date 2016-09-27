/* Copyright 2009-2016 EPFL, Lausanne */

package leon.annotation

import scala.annotation.StaticAnnotation

object grammar {

  @ignore
  class label extends StaticAnnotation

  @ignore
  class terminal(weight: Int) extends StaticAnnotation

  @ignore
  class production(weight: Int) extends StaticAnnotation

}
