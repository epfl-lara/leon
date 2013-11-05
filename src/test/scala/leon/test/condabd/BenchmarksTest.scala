/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package condabd

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.synthesis._
import leon.synthesis.utils._
import leon.synthesis.condabd.rules._

import org.scalatest.matchers.ShouldMatchers._

import util._

import java.io.{BufferedWriter, FileWriter, File}

class BenchmarksTest extends LeonTestSuite {
  
  import Utils._
  import Scaffold._
  
  def recursiveListFiles(f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }
  
  val benchmarkDir = "testcases/condabd/benchmarks"
    
  for( benchFile <- recursiveListFiles(new File(benchmarkDir)); if benchFile.getName contains "InsertionSortSort" ) {
    
    test ("benchFile: " + benchFile.getAbsolutePath) {
      val problems = forFile(benchFile.getAbsolutePath)
      
      problems.size should be (1)
      val (sctx, funDef, p) = problems.head
      
      val insts = ConditionAbductionSynthesisTwoPhase.instantiateOn(sctx, p)
      
      insts.size should be (1)
      insts.head.apply(sctx)
    }
    
  }  
  
}