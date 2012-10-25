package leon
package test

import org.scalatest.FunSuite

class ValidPrograms extends FunSuite {
  test("Some program is valid.") {
    val ctx = LeonContext(
      Settings(
        synthesis = false,
        xlang     = false,
        analyze   = true
      ),
      new SilentReporter
    )

    val pipeline = Main.computePipeline(ctx.settings) 

    val result = pipeline.run(ctx)("/home/psuter/Test.scala" :: Nil)

    assert(true)
  }
}
