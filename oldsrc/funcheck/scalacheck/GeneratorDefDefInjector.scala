package funcheck.scalacheck

import scala.tools.nsc.transform.TypingTransformers

trait GeneratorDefDefInjector extends TypingTransformers { 
   import global._
  
  def injectGenDefDefs(injecting: List[DefDef], unit: CompilationUnit): Unit = 
    unit.body = new GenDefDefTransformer(injecting, unit).transform(unit.body)
  
  class GenDefDefTransformer(injecting: List[DefDef], unit: CompilationUnit) 
    extends /*Code Injection*/ TypingTransformer(unit) 
  { 
    override def transform(tree: Tree): Tree = { 
      curTree = tree
      tree match {
        
        case impl @ Template(parents, self, body) => 
          atOwner(currentOwner) {
       	    val newBody: List[Tree] = body ::: (injecting.map(localTyper.typed(_)))  
            val cd = copy.Template(impl, parents, self, newBody)
            cd
          }
         
        /** Delegates the recursive traversal of the tree. */
       	case _ => super.transform(tree)
      }
    }
       
  }
} 
    
   