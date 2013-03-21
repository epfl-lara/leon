package lesynth

import scala.util.Random

import org.junit.Assert._
import org.junit.{ Test, Ignore }

import insynth.leon.HoleFinder
import insynth.leon.loader.LeonLoader

import _root_.leon.purescala.Trees.{ Hole, IntLiteral }
import _root_.leon.purescala.TreeOps
import _root_.leon.evaluators._
import _root_.leon.{ LeonContext, DefaultReporter, Main }
import _root_.leon.verification.AnalysisPhase

import insynth.testutil.CommonUtils
import testutil.TestConfig

class AnalyzerTest {

  import TestConfig._
  import CommonUtils._
  import TreeOps._
  
  val rnd = new Random(System.currentTimeMillis())
	
	@Test
	def testModel = {
    val holeFinder = new HoleFinder(lesynthTestDir + "ListOperations.scala")
				
    holeFinder.extract match {
      case Some((prog, hole)) =>
		
	    val reporter = new DefaultReporter()
		  val args = Array("testcases/insynth/ListOperations.scala", "--timeout=2")
		  
			val ctx = Main.processOptions(reporter, args.toList)
			
	    val verReport = AnalysisPhase.run(ctx)(prog)
	     
	    assertTrue(Globals.asMap.size > 0)
        
      case _ =>
        fail("HoleFinder could not extract hole from the program")
    }    
	}
  
}
