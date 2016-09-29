/* Copyright 2009-2016 EPFL, Lausanne */

package leon.annotation

import scala.annotation.StaticAnnotation

object grammar {

  @ignore
  class label extends StaticAnnotation

  @ignore
  class weight(weight: Int) extends StaticAnnotation

  @ignore
  class terminal extends StaticAnnotation

  @ignore
  class production extends StaticAnnotation

  @ignore
  class commutative extends StaticAnnotation

}
