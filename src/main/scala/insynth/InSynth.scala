package insynth

import insynth.reconstruction.stream.{ OrderedStreamFactory, UnorderedStreamFactory }
import insynth.reconstruction.codegen.CodeGenerator
import insynth.reconstruction.Reconstructor

import insynth.interfaces.Declaration
import insynth.engine.InitialEnvironmentBuilder

import insynth.leon.loader.LeonLoader
import insynth.leon.LeonQueryBuilder

import _root_.leon.purescala.Definitions.Program
import _root_.leon.purescala.Trees.Hole
import _root_.leon.purescala.TypeTrees.{ TypeTree => Type }

import insynth.util.logging.HasLogger

/**
 * Main class for the synthesis process invocation
 * @param program Leon program object that contains the hole
 * @param hole hole in the program on which the synthesis is called 
 */
class InSynth(declarations: List[Declaration], goalType: Type, ordered: Boolean = true) extends HasLogger {
  
//  def this(program: Program, hole: Hole, ordered: Boolean) =
//    this(new LeonLoader(program, hole).load, hole.getType, ordered)
    
  def this(loader: LeonLoader, ordered: Boolean) =
    this(loader.load, loader.hole.getType, ordered)
  
  lazy val solver = new Solver(declarations, new LeonQueryBuilder(goalType))
  
  def getExpressions = {
    val proofTree = solver.getProofTree
    	
		assert(proofTree != null, "Proof tree is null" )  
    assert(1 == proofTree.getNodes.size)
          
    val codegen = new CodeGenerator
    
    Reconstructor(proofTree.getNodes.head, codegen, ordered)
  }
  
  def getExpressions(builder: InitialEnvironmentBuilder) = {
    val proofTree = solver.getProofTree(builder)
    	
		assert(proofTree != null, "Proof tree is null" )  
    assert(1 == proofTree.getNodes.size)
          
    val codegen = new CodeGenerator
    
    Reconstructor(proofTree.getNodes.head, codegen, ordered)
  }
  
  def getCurrentBuilder = solver.currentBuilder

}

object InSynth {
  
  def apply(declarations: List[Declaration], goalType: Type, ordered: Boolean) =
    new InSynth(declarations, goalType, ordered)
  
//  def apply(program: Program, hole: Hole, ordered: Boolean) =
//    new InSynth(new LeonLoader(program, hole).load, hole.getType, ordered)
    
  def apply(loader: LeonLoader, ordered: Boolean) =
    new InSynth(loader.load, loader.hole.getType, ordered)
  
}