package funcheck.lib

object Specs {
  
  /** 
   * this is used to annotate the (unique) class method 
   * that will be used by our funcheck plugin to 
   * automagically define a class generator that can be used 
   * by ScalaCheck to create test cases.
   */ 
  class generator extends StaticAnnotation

  implicit def extendedBoolean(b: Boolean) = new {
    def ==>(p: Boolean) = Specs ==> (b,p)
  }
  
  def forAll[A](f: A => Boolean): Boolean =  
    error("\"forAll\" combinator is currently unsupported by plugin.")


  /** Implication */
  def ==>(ifz: => Boolean, then: Boolean): Boolean =  
    error("\"==>\" (implication) combinator is currently unsupported by plugin.")
  
}
