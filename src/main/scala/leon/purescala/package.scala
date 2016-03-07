/* Copyright 2009-2016 EPFL, Lausanne */

package leon

/** Provides AST definitions for Leon programs.
  *
  * The core language supported by Leon is called Pure Scala and its 
  * [[leon.purescala.Definitions]] and [[leon.purescala.Expressions]] are defined here.
  * This package also contains the [[leon.purescala.Types]] definitions. Each of those
  * trees come with a corresponding set of operations in the ???Ops objects.
  *
  * The package also provides general utilities operations on Pure Scala programs, such as
  * a method lifting phase [[leon.purescala.MethodLifting]] (transforming methods into 
  * top level functions) and a function closure phase [[leon.purescala.FunctionClosure]]
  * (lifting an inner function to the top level).
  *
  * Two printers for Pure Scala programs are also provided, a [[leon.purescala.PrettyPrinter]]
  * that outputs a nice and readable program (typically using unicode for some operations) and
  * a [[leon.purescala.ScalaPrinter]] that outputs a valid Scala program from a Leon 
  * representation.
  */
package object purescala {

}
