package lesynth

import util.control.Breaks._
import scala.collection._

import leon.purescala.Trees.{ Variable => LeonVariable, _ }

class Ranker(candidates: Seq[Expr], evaluation: Evaluation, printStep: Boolean = false) {
  
  var rankings: Array[Int] = (0 until candidates.size).toArray
  
  // keep track of intervals
  var tuples: Map[Int, (Int, Int)] =
    (for (i <- 0 until candidates.size)
      yield (i, (0, evaluation.getNumberOfExamples))) toMap
  
  def getKMax(k: Int) = {
    
  }
  
  def evaluate(ind: Int) {    
    val tuple = tuples(ind)
    val expr = ind
    
    tuples += ( ind ->
	    {
	      if (evaluation.evaluate(expr)) {
		      (tuple._1 + 1, tuple._2)
		    } else {
		      (tuple._1, tuple._2 - 1)	      
		    }
	    }
    )
      
  }
  
  def swap(ind1: Int, ind2: Int) = {
    val temp = rankings(ind1)
    rankings(ind1) = rankings(ind2)
    rankings(ind2) = temp
  }
  
  def bubbleDown(ind: Int): Unit = {
    if (compare(rankings(ind), rankings(ind + 1))) {
    	swap(ind, ind + 1)
    	if (ind < candidates.size-2)
    		bubbleDown(ind + 1)
    }      
  }
    
  var numberLeft = candidates.size
  
  def getMax = {
    
    numberLeft = candidates.size
    
    while (numberLeft > 1) {
      
      evaluate(rankings(0))
      
      if (printStep) {
	      println(printTuples)
	      println("*** left: " + numberLeft)
      }
      
      bubbleDown(0)
    
      val topRank = rankings(0)
      var secondRank = rankings(1)
      
      while (strictCompare(secondRank, topRank) && numberLeft > 1) {
      	numberLeft -= 1
      	swap(1, numberLeft) 
        secondRank = rankings(1)
      }
      
    }
    
    if (printStep) {
      println(printTuples)
      println("***: " + numberLeft)
    }
    
    candidates(rankings(0))
    
  }
  
//  def getVerifiedMax = {    
//    val results = (for (candidate <- 0 until candidates.size)
//  		yield (candidate,
//	  		(0 /: (0 until evaluation.getNumberOfExamples)) {
//	      	(res, exampleInd) =>
//			      if (evaluation.evaluate(candidate, exampleInd)) {
//				      res + 1
//				    } else {
//				      res	      
//				    }
//	    	}))
//	    	
//  	val maxPassed = results.sortWith((r1, r2) => r1._2 < r2._2)(candidates.size - 1)._2
//  	
//  	(results.filter(_._2 == maxPassed).map(x => candidates(x._1)), results)//.map(x => candidates(x._1))
//  }
  
  def strictCompare(x: Int, y: Int) = {
    val tuple1 = tuples(x)
    val tuple2 = tuples(y)
    
    tuple1._2 <= tuple2._1
  }
  
  def compare(x: Int, y: Int) = {
    val tuple1 = tuples(x)
    val tuple2 = tuples(y)
    
    val median1 = (tuple1._1 + tuple1._2).toFloat/2
    val median2 = (tuple2._1 + tuple2._2).toFloat/2
    
    /*median1 < median2 || median1 == median2 && */
    tuple1._2 < tuple2._2 || tuple1._2 == tuple2._2 && median1 < median2
  }
  
  def rankOf(expr: Int) =
    rankings.indexOf(expr)
  
  def printTuples =
    (for ((tuple, ind) <-
      tuples.toList.sortWith((tp1, tp2) => rankOf(tp1._1) <= rankOf(tp2._1)).zipWithIndex)
      yield (if (tuple._1 == rankings(0)) "->" else if (ind >= numberLeft) "/\\" else "  ") + tuple._1 +
      	": " +
      	((0 until evaluation.getNumberOfExamples) map {
      		x => if (x < tuple._2._1) '+' else if (x >= tuple._2._2) '-' else '_'
  		  }).mkString).mkString("\n")
	
}