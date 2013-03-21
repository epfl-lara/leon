package insynth.reconstruction

import insynth.structures.{ SimpleNode, Weight }
import insynth.reconstruction.intermediate.IntermediateTransformer
import insynth.reconstruction.stream.{ Node => LambdaNode, _ }
import insynth.reconstruction.codegen.CodeGenerator

import insynth.Config
import insynth.util.format.{ FormatSuccinctNode, FormatIntermediate, FormatStreamUtils }
import insynth.util.logging.HasLogger

/**
 * Object for reconstruction of proof trees into output(s)
 */
object Reconstructor extends ( (SimpleNode, CodeGenerator, Boolean) => Stream[Output]) with HasLogger {

  def apply(tree: SimpleNode, codeGenerator: CodeGenerator, streamOrdered: Boolean = false) = {		    
    // logging
    entering("apply", FormatSuccinctNode(tree, 8).toString)
    
    // transform the trees (first two steps of the code generation phase)
    val transformedTree = IntermediateTransformer(tree)
         
    // logging
    info("intermediate transform phase done")    
    fine("after intermediate " + FormatIntermediate(transformedTree))
    
    // create an ordered/unordered extractor
    val extractor = 
      if (streamOrdered)
        new Extractor(new OrderedStreamFactory[LambdaNode])
      else
        new Extractor(new UnorderedStreamFactory[LambdaNode])
                
    // generate streams of lambda trees
    val extractedTrees = extractor(transformedTree)
    
    // logging
    info("extractor phase done")
    fine("got streamable " + FormatStreamUtils(extractor.transformedStreamable))
    
    // for each tree, generate the code for it
    val generatedCode = extractedTrees map {
      resPair => Output(codeGenerator(resPair._1), resPair._2)
    }
        
    // logging
    info("solutions are generated")
    
    generatedCode
  }
  
}
