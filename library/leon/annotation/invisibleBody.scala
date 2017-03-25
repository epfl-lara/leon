/* Copyright 2009-2016 EPFL, Lausanne */
package leon.annotation

import scala.annotation.StaticAnnotation

@ignore
class invisibleBody extends StaticAnnotation // do not unfold the body of the function
