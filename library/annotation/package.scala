/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

package object annotation {
  @ignore
  class library    extends StaticAnnotation
  @ignore
  class repair     extends StaticAnnotation
  @ignore
  class induct     extends StaticAnnotation
  @ignore
  class extern     extends StaticAnnotation
  @ignore
  class ignore     extends StaticAnnotation
}

