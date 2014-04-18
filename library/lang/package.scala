/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import leon.annotation._
import scala.language.implicitConversions

package object lang {
  @ignore
  sealed class IsValid(val property : Boolean) {
    def holds : Boolean = {
      assert(property)
      property
    }
  }

  @ignore
  implicit def any2IsValid(x: Boolean) : IsValid = new IsValid(x)

  @ignore
  object InvariantFunction {
    def invariant(x: Boolean): Unit = ()
  }

  @ignore
  implicit def while2Invariant(u: Unit) = InvariantFunction

  @ignore
  def error[T](reason: String): T = sys.error(reason)
    
  /*sealed class TemplateCons(val postcond : Boolean) {
    //TODO allow elegant ways of supporting templates with arbitrary number of arguments    
    def template(templateFunc : Float => Boolean) : Boolean = postcond    
    def template(templateFunc : (Float,Float) => Boolean) : Boolean = postcond    
    def template(templateFunc : (Float,Float, Float)  => Boolean) : Boolean = postcond    
    def template(templateFunc : (Float,Float, Float, Float)  => Boolean) : Boolean = postcond    
    def template(templateFunc : (Float,Float, Float, Float, Float)  => Boolean) : Boolean = postcond    
    def template(templateFunc : (Float,Float, Float, Float, Float, Float)  => Boolean) : Boolean = postcond
  }*/

  @ignore
  sealed class TemplateCons(val postcond : Boolean) {
    //TODO allow elegant ways of supporting templates with arbitrary number of arguments    
    def template(templateFunc : Int => Boolean) : Boolean = postcond    
    def template(templateFunc : (Int,Int) => Boolean) : Boolean = postcond    
    def template(templateFunc : (Int,Int, Int)  => Boolean) : Boolean = postcond    
    def template(templateFunc : (Int,Int, Int, Int)  => Boolean) : Boolean = postcond    
    /*def template(templateFunc : (Float,Float, Float, Float, Float)  => Boolean) : Boolean = postcond    
    def template(templateFunc : (Float,Float, Float, Float, Float, Float)  => Boolean) : Boolean = postcond*/
  }
  
  @ignore
  implicit def any2Template(postcond: Boolean): TemplateCons = {    
    new TemplateCons(postcond)
  }
  
  //a counter that counts the number of time steps
  @ignore
  def time: Int = throw new RuntimeException("Implementation not supported")
  
  //a counter that counts the depth
  @ignore
  def depth: Int = throw new RuntimeException("Implementation not supported")
}
