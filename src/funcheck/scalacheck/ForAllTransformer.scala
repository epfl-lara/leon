package funcheck.scalacheck

import scala.tools.nsc.transform.TypingTransformers

import funcheck.util.FreshNameCreator 

trait ForAllTransformer extends TypingTransformers
  with ScalaCheck
  with FreshNameCreator 
{ 
  import global._
  
  private lazy val specsModule: Symbol = definitions.getModule("funcheck.lib.Specs")
  
  
  
  def forAllTransform(unit: CompilationUnit): Unit = 
    unit.body = new ForAllTransformer(unit).transform(unit.body)
    
    
  class ForAllTransformer(unit: CompilationUnit) 
    extends TypingTransformer(unit) 
  { 
    override def transform(tree: Tree): Tree = {
      curTree = tree
       
      tree match {
        case Apply(TypeApply(s: Select, partpes), rhs @ List(f @ Function(vparams,body))) if isForall(s) =>
          atOwner(currentOwner) {
            assert(vparams.size == 1, "funcheck.Specs.forAll properties are expected to take a single (tuple) parameter")
            
            val v @ ValDef(mods,name,vtpt,vinit) = vparams.head
            
            partpes.head.tpe match {
              case tpe @ TypeRef(_,_,ptpes) =>
                vtpt.tpe match {
                  case TypeRef(_,value,vtpes) =>
                    val fun: Function = {
                      if(vtpes.size <= 1) {
                        f
                      } else {
                      
                        // create a fresh name for each parameter declared parametric type
                        val freshNames = vtpes.map(i => fresh.newName("v"))
                      
                        val funSym = tree.symbol
                      
                        val subst = for { i <- 0 to vtpes.size-1} yield {
                          val toSym = funSym.newValueParameter(funSym.pos, freshNames(i)).setInfo(vtpes(i))
                        
                          val from = Select(v, v.symbol.tpe.decl("_"+(i+1)))
                          val to =  ValDef(toSym, EmptyTree) setPos (tree.pos)                        
                        
                          (from, to)
                        } 
                      
                      
                        val valdefs = subst.map(_._2).toList
                        val fun = localTyper.typed {
                          val newBody = new MyTreeSubstituter(subst.map(p => p._1.symbol).toList, valdefs.map(v => Ident(v.symbol)).toList).transform(resetAttrs(body))
                          Function(valdefs, newBody)
                        }.asInstanceOf[Function]
                      
                      
                        new ChangeOwnerTraverser(funSym, fun.symbol).traverse(fun);
                        new ForeachTreeTraverser({t: Tree => t setPos tree.pos}).traverse(fun)
                        fun
                     }
                   }
                   
                   val prop = Prop.forAll(List(fun))
                      
                   var buf = new collection.mutable.ListBuffer[Tree]()
                      
                   val blockValSym = newSyntheticValueParam(fun.symbol, definitions.BooleanClass.typeConstructor)
                      
                   val fun2 = localTyper.typed {
                     val body = Prop.propBoolean(resetAttrs(Ident(blockValSym)))
                     Function(List(ValDef(blockValSym, EmptyTree)), body)
                   }.asInstanceOf[Function]
                       
                   
                   new ChangeOwnerTraverser(fun.symbol, fun2.symbol).traverse(fun2);
                   new ForeachTreeTraverser({t: Tree => t setPos tree.pos}).traverse(fun2)
                      
                   buf += Block(Nil,fun2)
                               
                   if(vtpes.isEmpty) {
                     buf += resetAttrs(Arbitrary.arbitrary(value.tpe))
                     buf += resetAttrs(Shrink.shrinker(value.tpe))
                   } else {  
                     for {tpe <- vtpes} {
                       buf += resetAttrs(Arbitrary.arbitrary(tpe))
                       buf += resetAttrs(Shrink.shrinker(tpe))
                     }
                   }

                   import posAssigner.atPos         // for filling in tree positions

                   
                   val property = localTyper.typed {
                     atPos(tree.pos) {
                       Apply(prop, buf.toList)
                     }
                   }
                      
                   
                    
                   localTyper.typed {
                     atPos(tree.pos) {
                       ConsoleReporter.testStatsEx(Test.check(property))
                     }
                   }
                    
                  case t => 
                    assert(false, "expected ValDef of type TypeRef, found "+t)
                    tree
                }
                
              case t => tree  
            }
          }
  
  	    /** Delegates the recursive traversal of the tree. */
       	case _ => super.transform(tree)
      }
      
    }
    
     class ChangeOwnerTraverser(val oldowner: Symbol, val newowner: Symbol) extends Traverser {
    override def traverse(tree: Tree) {
	      if (tree != null && tree.symbol != null && tree.symbol != NoSymbol && tree.symbol.owner == oldowner)
	        tree.symbol.owner = newowner;
	      super.traverse(tree)
	    }
	  }
    
    /** Synthetic value parameters when parameter symbols are not available
    */
    final def newSyntheticValueParam(owner: Symbol, argtype: Type): Symbol = {
      var cnt = 0
      def freshName() = { cnt += 1; newTermName("x$" + cnt) }
      def param(tp: Type) =
    	  owner.newValueParameter(owner.pos, freshName()).setFlag(scala.tools.nsc.symtab.Flags.SYNTHETIC).setInfo(tp)
      param(argtype)
    }
    
    
    private def isForall(s: Select): Boolean = {
      val Select(selector,_) = s
     
       selector.symbol == specsModule &&
       s.symbol == specsModule.tpe.decl("forAll")
    }
    
    
    /** Quick (and dirty) hack for enabling tree substitution for pair elements.
     * Specifically, this allow to map pair accesses such as p._1 to a new variable 'x'
     * ([p._1 |-> x, p._2 |-> y, ..., p._n |-> z])
     */
    class MyTreeSubstituter(from: List[Symbol], to: List[Tree]) extends TreeSubstituter(from,to) {
      override def transform(tree: Tree): Tree = tree match {
        // Useful for substutite values like p._1 where 'p' is a pair
        // Inherithed 'TreeSubstituter' cannot handle this
	    case Select(Ident(_), name) =>
          def subst(from: List[Symbol], to: List[Tree]): Tree =
            if (from.isEmpty) tree
            else if (tree.symbol == from.head) to.head
            else subst(from.tail, to.tail);
          subst(from, to)
	    case _ =>
          super.transform(tree)
      }
    }
    
  }
  
}
