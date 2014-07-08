package leon.test.memoization

// Which tests we are performing
object MemoTestOptions {

  val testSizesAndRepetitions = Seq(
    (100,100),
    (250,100),
    (500,50),
    (1000,30),
    (1500,25),
    (2000,20)
  )

  val testOutputValidity  = true  // Test if output file is valid (Pure)Scala
  val testWithVerify      = true  // Verify programs and only memoize unproven functions
  val testOutputs         = true // See if program outputs match + performance

  val testOriginal        = false// False to test only new, if original is too slow
  val testOriginalR       = false
  val testTrans           = false
  val testTransR          = true

  val applyTransform      = true  // Apply memo transform (false if you have outputs)
  val testInc             = true // Test incremental benchmarks
  val testBulk            = true  // Test bulk benchmarks
  val testPoly            = false
  val library             = false
  
  class HowToTest extends Enumeration
  case object Incremental extends HowToTest // e.g. insertions, one after the other
  case object Bulk        extends HowToTest // e.g. sorting, one time
}
