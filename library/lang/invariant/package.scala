/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lang

import leon.annotation._
import scala.language.implicitConversions

package object invariantLang {  
  
  @ignore
  def nondet[T]: T =  throw new RuntimeException("Implementation not supported")
  
  //def assume(cond: Boolean) : Unit = throw new RuntimeException("Implementation not supported")
      
  //the following class represents a template definition
  @ignore
  class TemplateCons(val postcond : Boolean) {
    //TODO allow elegant ways of supporting templates with arbitrary number of arguments    
    def template(templateFunc : Float => Boolean) : Boolean = postcond
    def template(templateFunc : (Float,Float) => Boolean) : Boolean = postcond
    def template(templateFunc : (Float,Float, Float)  => Boolean) : Boolean = postcond
    def template(templateFunc : (Float,Float, Float, Float)  => Boolean) : Boolean = postcond
    def template(templateFunc : (Float,Float, Float, Float, Float)  => Boolean) : Boolean = postcond
    def template(templateFunc : (Float,Float, Float, Float, Float, Float)  => Boolean) : Boolean = postcond
  }
  
  @ignore
  implicit def any2Template(postcond: Boolean): TemplateCons = new TemplateCons(postcond)
  
  //a counter that counts the number of time steps
  @ignore
  def time: Int = throw new RuntimeException("Implementation not supported")
  
  //a counter that counts the depth
  @ignore
  def depth: Int = throw new RuntimeException("Implementation not supported")
}
