package funcheck

/** 
 * A tree traverser which filter the trees elements that contain the 
 * <code>@generator</code> annotation, defined in <code>funcheck.lib.Specs</code> 
 * module.  
 * 
 * Note: For the moment this is working only for <code>ClassDef</code> and 
 * <code>DefDef</code> tree elements.  
 *  
 * This trait is meant to be used with the <code>FilterTreeTraverser</code> 
 * class, available in the <code>scala.tools.nsc.ast.Trees</code> trait. 
 * 
 * 
 * Usage Example:
 * 
 * new FilterTreeTraverser(filterTreesWithGeneratorAnnotation(unit))
 * 
 * where <code>unit</code> is the current Compilation Unit.
 */
trait FilterGeneratorAnnotations { self: AnalysisComponent =>
  // [[INFO]] "hasAttribute" is "hasAnnotation" in future compiler release 2.8
  import global._
  
  /** Funcheck <code>@generator</code> annotation. */
  private lazy val generator: Symbol = definitions.getClass("funcheck.lib.Specs.generator")
  
  
  /**
   * Check for <code>@generator</code> annotation only for class and method 
   * definitions. A class is considered to be annotated if either the class itself 
   * has the annotation, or if the class inherit from an annotated abstract class.
   */
  def filterTreesWithGeneratorAnnotation(Unit: CompilationUnit)(tree: Tree): Boolean = {
    lazy val sym = tree.symbol
    tree match {
      case cd: ClassDef => sym.hasAttribute(generator) || abstractSuperClassHasGeneratorAnnotation(sym.superClass)
      case d: DefDef    => sym.hasAttribute(generator)
      case _ => false
    }
  }
  
  
  /** Return true if the class (or superclass) symbol is flagged as being ABSTRACT and contains 
   * the <code>@generator</code> annotation.*/
  private def abstractSuperClassHasGeneratorAnnotation(superclass: Symbol): Boolean = { 
    //require(superclass.isInstanceOf[ClassSymbol], "expected ClassSymbol, found "+superclass)
    superclass match {
      case NoSymbol => false
      case cs: ClassSymbol =>
        (cs.hasFlag(scala.tools.nsc.symtab.Flags.ABSTRACT) &&  
           cs.hasAttribute(generator)) || 
          abstractSuperClassHasGeneratorAnnotation(cs.superClass)
      case _ => 
        assert(false, "expected ClassSymbol, found "+superclass)
        false
    }
    
  }
}
