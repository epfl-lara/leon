/* Copyright 2009-2016 EPFL, Lausanne */
package leon.annotation

import scala.annotation.StaticAnnotation
import scala.Int

@ignore
class unfoldFactor(f: Int=0) extends StaticAnnotation // 0 implies no bound on unfolding
