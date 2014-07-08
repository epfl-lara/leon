/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

package object annotation {
  @ignore
  class library    extends StaticAnnotation
  @ignore
  class verified   extends StaticAnnotation

  @ignore
  class induct     extends StaticAnnotation
  @ignore
  class axiomatize extends StaticAnnotation
  @ignore
  class main       extends StaticAnnotation
  @ignore
  class extern     extends StaticAnnotation
  @ignore
  class ignore     extends StaticAnnotation

  @ignore
  class forceMemo  extends StaticAnnotation
}

