/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import scala.annotation.StaticAnnotation

package object annotation {
  @ignore
  class library    extends StaticAnnotation
  @ignore
  class induct     extends StaticAnnotation
  @ignore
  class traceInduct(name: String = "") extends StaticAnnotation
  @ignore
  class ignore     extends StaticAnnotation
  @ignore
  class extern     extends StaticAnnotation
  @ignore
  class inline     extends StaticAnnotation
  @ignore
  class internal   extends StaticAnnotation

  // Orb annotations
  @ignore
  class monotonic  extends StaticAnnotation
  @ignore
  class compose    extends StaticAnnotation
  @ignore
  class axiom 		extends StaticAnnotation
  @ignore
  class invstate extends StaticAnnotation
  @ignore
  class memoize extends StaticAnnotation
  @ignore
  class invisibleBody extends StaticAnnotation // do not unfold the body of the function
  @ignore
  class usePost extends StaticAnnotation // assume the post-condition while proving time bounds
  @ignore
  class unfoldFactor(f: Int=0) extends StaticAnnotation // 0 implies no bound on unfolding
}