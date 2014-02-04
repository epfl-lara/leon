/* Copyright 2009-2013 EPFL, Lausanne */

package leon

case class LeonFatalError(msg: String) extends Exception(msg)
