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
    
    
//    val cdSym = c.symbol
//         if(cdSym.hasFlag(ABSTRACT)) { 
//           DefGenerator.addAbstr(c)
//           println(cdSym.children)
//         }
//         else {
//           val Template(_, _, body) = impl
//           for { b <- body } b match {
//             case d @ DefDef(_, nme.CONSTRUCTOR, _, _, _, _) =>
//               DefGenerator.addDef(d)
//             case _ => ;
//           }
//         }
  
  
   
   //   lazy val specsModule: Symbol = definitions.getModule("funcheck.lib.Specs")
   //val neededGenerators = scala.collection.mutable.Set.empty[Symbol]
   
   
   /*********************************************************************************/
//   private def isForall(s: Select): Boolean = {
//     val Select(selector,_) = s
//     
//     selector.symbol == specsModule &&
//     s.symbol == specsModule.tpe.decl("forAll")
//   }
//   
//    
//   /*********************************************************************************/
//   def collectProperties(Unit: CompilationUnit)(tree: Tree): Unit = tree match {
//     case TypeApply( s: Select, tpes: List[Tree]) =>
//       if(isForall(s)) {
//         for { treeTpe <- tpes } treeTpe.tpe match {
//           case TypeRef(_, _, args: List[Type]) => 
//             for {arg <- args} arg match {
//               case TypeRef(_,sym,_) => {
//                 //generators are needed only for user-defined types (assuming Pure Scala as input language)   
//                 if (!definitions.isValueClass(sym)) 
//                   neededGenerators += sym
//               }
//               case _ => error("Don't know what to do with "+ arg)
//             }
//           case _ => error("don't know what to do with " + treeTpe + " with associated symbol: "+treeTpe.symbol)
//         }
//         //println(neededGenerators)
//       } 
//       
//     case _ =>
//   }
   
   
 
