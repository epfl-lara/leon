package insynth

import insynth.reconstruction.stream.{ OrderedStreamFactory, UnorderedStreamFactory }
import insynth.reconstruction.codegen.CodeGenerator
import insynth.reconstruction.Reconstructor

import insynth.engine.InitialEnvironmentBuilder

import insynth.leon.{ LeonDeclaration => Declaration }
import insynth.leon.loader.LeonLoader
import insynth.leon.LeonQueryBuilder

import _root_.leon.purescala.Definitions.Program
import _root_.leon.purescala.TypeTrees.{ TypeTree => Type }

import insynth.util.logging.HasLogger

/**
 * Main class for the synthesis process invocation
 * @param program Leon program object that contains the hole
 * @param hole hole in the program on which the synthesis is called 
 */
class InSynth(_declarations: List[Declaration], goalType: Type, ordered: Boolean = true) extends HasLogger {
  
  def declarations = _declarations
  
//  def this(program: Program, hole: Hole, ordered: Boolean) =
//    this(new LeonLoader(program, hole).load, hole.getType, ordered)
    
  def this(loader: LeonLoader, goalType: Type, ordered: Boolean) =
    this(loader.load, goalType, ordered)
  
  lazy val solver = new Solver(declarations, new LeonQueryBuilder(goalType))
  
  def getExpressions = {
    info("InSynth synthesizing type + " + goalType + " with declarations " + solver.allDeclarations.mkString("\n"))
    val proofTree = solver.getProofTree
    	
		assert(proofTree != null, "Proof tree is null" )  
    assert(1 == proofTree.getNodes.size)
          
    val codegen = new CodeGenerator
    
    Reconstructor(proofTree.getNodes.head, codegen, ordered)
  }
  
  def getExpressions(builder: InitialEnvironmentBuilder) = {
    info("InSynth synthesizing type + " + goalType + " with declarations " + builder.getAllDeclarations.mkString("\n"))
    val proofTree = solver.getProofTree(builder)
    info("Proof tree is acquired")
    	
		assert(proofTree != null, "Proof tree is null" )  
    assert(1 == proofTree.getNodes.size)
          
    val codegen = new CodeGenerator
    
    Reconstructor(proofTree.getNodes.head, codegen, ordered)
  }
  
  def getCurrentBuilder = solver.currentBuilder

  def getAllDeclarations = _declarations

}

object InSynth {
  
  def apply(declarations: List[Declaration], goalType: Type, ordered: Boolean) =
    new InSynth(declarations, goalType, ordered)
  
  def apply(loader: LeonLoader, goalType: Type, ordered: Boolean) =
    new InSynth(loader.load, goalType, ordered)
  
}