package insynth.reconstruction

import insynth.structures.{ SimpleNode, Weight }
import insynth.reconstruction.shortcut._
import insynth.reconstruction.stream.{ Node => LambdaNode, _ }
import insynth.reconstruction.codegen.CodeGenerator

import insynth.Config
import insynth.util.format.{ FormatSuccinctNode, FormatIntermediate, FormatStreamUtils }
import insynth.util.logging.HasLogger
import insynth.util._

/**
 * Object for reconstruction of proof trees into output(s)
 */
object FastReconstructor extends ( (SimpleNode, CodeGenerator, Boolean) => Stream[Output]) with HasLogger {

  def apply(tree: SimpleNode, codeGenerator: CodeGenerator, streamOrdered: Boolean = false) = {		    
    // logging
    entering("apply", FormatSuccinctNode(tree, 8).toString)
    fine("reconstructor got proof tree size: " + ProofTreeOperations.size(tree))
         
    // create an ordered/unordered extractor
    val transformer = 
      if (streamOrdered)
        new Transformer2(new OrderedStreamFactory[LambdaNode])
      else
        new Transformer2(new UnorderedStreamFactory[LambdaNode])
    
    // transform the trees (first two steps of the code generation phase)
    val extractedTrees = transformer(tree)
    
    // logging
    info("extractor phase done")
    
    // for each tree, generate the code for it
    val generatedCode = extractedTrees map {
      resPair => Output(codeGenerator(resPair._1), resPair._2)
    }
        
    // logging
    info("solutions are generated")
    
    generatedCode
  }
  
}
