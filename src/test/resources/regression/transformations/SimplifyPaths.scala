/* Copyright 2009-2014 EPFL, Lausanne */

import leon.annotation._
import leon.lang._
import leon.collection._

object Transform {


    def input01(a: Int): Int = {
      if(true) 1 else 2
    }

    def output01(a: Int): Int = {
      1
    }

    def input02(a: Boolean, b : Boolean, c : Boolean): Boolean = {
      (a && !b) == !(!a || b) match {
        case x@true => x && c
        case false => !c
      }
    }

    def output02(a: Boolean, b : Boolean, c : Boolean): Boolean = {
      c
    }

    def input03(a: List[Int]): Int = {
      a match {
        case Nil() => 0
        //case n if n.isEmpty => 1
        case Cons(x, y) => 1
        case Cons(x, Cons(y,z)) => 2
      }
    }

    def output03(a: List[Int]): Int = {
      a match {
        case Nil() => 0
        case Cons(x,y) => 1
      }
    }

    def input04(a: Int): Int = {
      a match {
        case 0 => 0
        case x if x >= 42 => x+42
        case y if y >  42 => y-42
        case z if z > 0 => z +100
        case w if w < 0 => w -100
        case other => 1000
      }
    }
    def output04(a: Int): Int = {
      a match {
        case 0 => 0
        case x if x >= 42 => x + 42
        case z if z > 0 => z+100
        case w => w-100
      }
    }

    def input05(a : Int) : Int = {
      a match {
        case x@_ => x
      }
    }

    def output05(a : Int) : Int = {
      a
    }
    
    def input06(a : (Int, Int)) : Int = {
      a match {
        case (x,y) => x
      }
    }

    def output06(a : (Int,Int)) : Int = {
      a._1
    }

    def input07(l : List[Int]) : Int = l match {
      case Nil() if false => 42
      case Cons(h,t) => h
    }

    def output07(l : List[Int]) : Int = l match {
      case Cons(h,t) => h
    }

}
