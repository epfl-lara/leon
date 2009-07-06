package funcheck.scalacheck

import scala.tools.nsc.{Global, SubComponent}


trait ScalaCheckIntegrator extends ScalaCheck 
  with FilterGeneratorAnnotations
  with GeneratorDefDefInjector
  with ForAllTransformer 
{
  val global: Global
  import global._
  
  
  def createGeneratorDefDefs(unit: CompilationUnit): (List[DefDef], List[DefDef]) = {
    val filteredGenTree = new FilterTreeTraverser(filterTreesWithGeneratorAnnotation(unit))
    filteredGenTree.traverse(unit.body)
    
    val klasses = collection.mutable.Set.empty[ClassDef]
    val defs = collection.mutable.Set.empty[DefDef]
    
    for {tree <- filteredGenTree.hits} tree match {
      case c: ClassDef => klasses + c
      case d: DefDef => defs + d
    }  
    
    (Gen.createGenDefDef(klasses.toList,defs.toList), Arbitrary.getArbitraryDefDefs)
  }
  
  
}
