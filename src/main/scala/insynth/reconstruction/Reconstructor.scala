package insynth.reconstruction

import insynth.structures.{ SimpleNode, Weight }
import insynth.reconstruction.stream.{ Node => LambdaNode, _ }

import insynth.reconstruction.codegen.CodeGenerator

import insynth.util.format.{ FormatSuccinctNode, FormatStreamUtils }
import insynth.util.logging.HasLogger
import insynth.util._

/**
 * Object for reconstruction of proof trees into output(s)
 */
object Reconstructor extends ( (SimpleNode, CodeGenerator, Boolean) => Stream[Output]) with HasLogger {

  def apply(tree: SimpleNode, codeGenerator: CodeGenerator, streamOrdered: Boolean = false) = {		    
    
    // transform the trees (first two steps of the code generation phase)
    val stream = Streamer(tree, streamOrdered)
         
    info("streamer done, stream computed")
    
    // for each tree, generate the code for it
    val generatedCode = stream map {
      resPair => Output(codeGenerator(resPair._1), resPair._2)
    }
        
    info("stream of solutions is generated")
    
    generatedCode
  }
  
}
