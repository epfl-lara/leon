package funcheck.scalacheck

import scala.tools.nsc.transform.TypingTransformers

trait ForAllTransformer extends TypingTransformers {
  import global._
  
  def forAllTransform(unit: CompilationUnit): Unit =
    unit.body = new ForAllTransformer(unit).transform(unit.body)
    
  class ForAllTransformer(unit: CompilationUnit) 
    extends /*Code Injection*/ TypingTransformer(unit) 
  { 
    override def transform(tree: Tree): Tree = null
  }
}
