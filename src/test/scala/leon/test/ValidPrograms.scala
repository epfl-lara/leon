package leon
package test

import org.scalatest.FunSuite

import java.io.File

class ValidPrograms extends FunSuite {
  def runBasicLeonOnFile(filename : String) : Unit = {
    val file = new File(filename)

    assert(file.exists && file.isFile && file.canRead,
           "Benchmark [%s] is not a readable file".format(filename))

    val ctx = LeonContext(
      Settings(
        synthesis = false,
        xlang     = false,
        analyze   = true
      ),
      new SilentReporter
    )

    val pipeline = Main.computePipeline(ctx.settings)
    pipeline.run(ctx)("--timeout=2" :: file.getPath :: Nil)
  }

  def mkTest(filename : String) = {
    test("Valid PureScala program: [%s]".format(filename)) {
      runBasicLeonOnFile(filename)
      assert(true)
    }
  }

  test("List files") {
    import scala.collection.JavaConversions._

    val ress = this.getClass.getClassLoader.getResources("/regression/verification/purescala/valid/")

    for(res <- ress) {
      println(res)
    }
  }

  mkTest("/home/psuter/Test.scala")
}
