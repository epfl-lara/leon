/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.frontends

import leon.test.LeonTestSuite
import leon._
import purescala.Definitions._
import purescala.ScalaPrinter
import frontends.scalac._
import utils._


class ImportsTests extends LeonTestSuite {
  private def parseStrings(strs : List[String]) : Program = {
    val settings : Settings = Settings(
      verify = false
    )
    val reporter = new DefaultReporter(settings)
    val context : LeonContext = LeonContext(
      reporter,
      new InterruptManager(reporter),
      settings,
      Seq()
    )
    
    val pipeline = 
      ExtractionPhase andThen 
      PreprocessingPhase 
      
    val inputs = strs map { str => TemporaryInputPhase.run(context)((str, Nil)).head }
    val program = pipeline.run(testContext)(inputs)
    
    program
  }
  
  // Print and reparse tests
  private def testPrint(name : String, strs : List[String]) { test(name){
    val orig = parseStrings(strs )
    val output = orig.units map { ScalaPrinter(_) }
    // If we can reparse, we consider it successful.
    val after = parseStrings(strs)
  }}
  
  val testPrint1 = ("testPrint1", List(
    """ |package foo.bar.baz
  	    |import other.hello.world.Foo._
  	    |
    		|object Bar {
    		|  val x = 42
    		|  abstract class A
    		|  case class C(i : Int) extends A
    		|}
    		|
    		|object Foo {
    		|  import Bar.C
    		|  case class FooC()
    		|  val m = Bar.x + y + x
    		|  val ? = C(m)
    		|  val fooC = ? match {
    		|    case C(i) if i == 0 => FooC()
    		|    case _ => FooC()
    		|  }
    		|}""".stripMargin,
	
  	""" |package other.hello.world
    		|
    		|object Foo {
    		|  val y = 0 
    		|}""".stripMargin,
  	
  	"""	|package foo.bar
    		|package object baz {
    		|  val x = 42 
    		|}""".stripMargin
  ))
  
  for ((name,units) <- Seq(testPrint1)) {
    testPrint(name, units)
  }
  
  
}



