package leon.test.condabd.insynth.testutil

import org.junit.Assert._

import leon.synthesis.condabd.insynth.reconstruction.Output

object CommonUtils {
    
  val maxElToOutput = 20
      
  def assertTake(stream: Stream[Output], num: Int) = {
    val result = stream take num
    val message = "Part of the resulting stream: " + result.take(maxElToOutput).mkString("\n")
    
    for (ind <- 0 until result.size - 1)
      assertTrue("Weight are not in non-decreasing order.\n" + "At position " + ind + "\n" + message, stream(ind).getWeight <= stream(ind + 1).getWeight)
    result
  }

}