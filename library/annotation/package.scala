/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

package object annotation {
  @ignore
  class library    extends StaticAnnotation
  @ignore
  class induct     extends StaticAnnotation
  @ignore
  class ignore     extends StaticAnnotation
  @ignore
  class extern     extends StaticAnnotation
  @ignore
  class inline     extends StaticAnnotation
  @ignore
  class monotonic  extends StaticAnnotation
  @ignore
  class compose    extends StaticAnnotation
}