/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lazyeval

import leon.annotation._

import scala.annotation.StaticAnnotation
import scala.Predef.String

/**
  * annotations for monotonicity proofs.
  * Note implemented as of now.
  * Let foo be the method that has the annotation.
  * The given name `methodname` should have the following form:
  *  m(arg1, ..., argn, substate-Set1,..., substate-Setn, superstate-Set1, ..., superstate-Setn)
  */
@ignore
class monoproof(methodname: String) extends StaticAnnotation
