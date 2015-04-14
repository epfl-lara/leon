/* Copyright 2009-2015 EPFL, Lausanne */

object Operators {
  
  case class HasOps(i : Int){
    def + (j : HasOps) = this.i + j.i
  }
  
  def x = HasOps(12) + HasOps(30)
  
}