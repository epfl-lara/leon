/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.purescala

import leon._
import purescala.Definitions._
import purescala.DefOps._
import purescala.ScalaPrinter
import frontends.scalac._
import utils._
import leon.test.LeonTestSuite

private [purescala] object DefOpsHelper extends LeonTestSuite { 
  private def parseStrings(strs : List[String]) : Program = {
    val settings : Settings = Settings(
      verify = false
    )
    val c = createLeonContext()
    val context : LeonContext = c.copy(settings = 
      c.settings.copy(verify = false)
    )
      
    val pipeline = 
      ExtractionPhase andThen 
      PreprocessingPhase 
      
    val inputs = strs map { str => TemporaryInputPhase.run(context)((str, Nil)).head }
    val program = pipeline.run(context)(inputs)
    
    program
  }

  val test1 = List(
    """ |package foo.bar.baz
        |import other.hello.world.Foo
        |import other.hello.world.Foo._
        |import other.hello.world.!!!._
        |import other.hello.world.m
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
        |object !!! { val m = 42 }
        |object m { val x = 0 }
        |
        |object Foo {
        |  val y = 0 
        |}""".stripMargin,
    
    """ |package foo.bar
        |package object baz {
        |  val x = 42 
        |}""".stripMargin,
        
    """ |package foo.bar.baz.and.some.more
        |object InSubpackage {}
        |""".stripMargin,

    """ object InEmpty { def arrayLookup(a : Array[Int], i : Int) = a(i) } """
  )
  val program = parseStrings(test1)
  val fooC = searchByFullName("foo.bar.baz.Foo.fooC",program)
}

class DefOpsTests extends LeonTestSuite {
    import DefOpsHelper._
    
    test("Find base definition"){assert(fooC.isDefined)}

    
    test("Least common ancestor"){
      val x = searchByFullName("foo.bar.baz.x",program)
      assert(x.isDefined)
      assert(leastCommonAncestor(x.get,fooC.get) == program)
      val fooClass = searchByFullName("foo.bar.baz.Foo.FooC",program)
      assert (fooClass.isDefined)
      assert(leastCommonAncestor(fooC.get, fooClass.get).id.name == "Foo")
    } 

    test("In empty package") { 
      val name = "InEmpty.arrayLookup"
      val df = searchByFullName(name,program)
      assert(df.isDefined)
      assert{fullName(df.get) == name } 
    }
    
    // Search by full name    
   
    def mustFind(name : String, msg : String) = test(msg) {assert(searchByFullNameRelative(name,fooC.get).isDefined) }
    def mustFail(name : String, msg : String) = test(msg) {assert(searchByFullNameRelative(name,fooC.get).isEmpty) }

    mustFind("fooC", "Find yourself")
    mustFind("FooC", "Find a definition in the same scope 1")
    mustFind("?",    "Find a definition in the same scope 2")
    mustFind("m",    "Find a definition in the same scope 3")
    mustFind("Foo",  "Find an enclosing definition")
    mustFind("Bar",  "Find a definition in an enclosing scope")
 
    mustFind("Bar.A",    "Find a definition in an object 1")
    mustFind("Foo.fooC", "Find a definition in an object 2")

    mustFind("y", "Find imported definition 1")
    mustFind("x", "Find imported definition 2")
    
    mustFind("other.hello.world.Foo",     "Find a definition in another package")
    mustFind("and.some.more.InSubpackage","Find a definition in a subpackage")
    mustFind("InEmpty.arrayLookup",       "Find a definition in the empty package")

    mustFail("nonExistent",    "Don't find non-existent definition")
    mustFail("A",              "Don't find definition in another object")
    mustFail("InSubpackage",   "Don't find definition in another package")
    mustFail("hello.world.Foo","Don't find definition in non-visible nested package")
    mustFail("!!!",            "Don't find definition that is root of a wildcard import")
    mustFail("m.x",            "Don't find imported definition shadowed by local definition")
      
}
