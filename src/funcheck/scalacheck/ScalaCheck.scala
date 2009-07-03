package funcheck.scalacheck

import scala.tools.nsc.{Global, SubComponent}

/**
 * Utilitarity class that is used as a factory for creating Tree nodes for method 
 * calls of classes and modules in the <code>org.scalacheck</code> package. 
 */
trait ScalaCheck[T <: SubComponent] {self: T =>
  import global._
  
  
  /** Transform string name in method symbols from the <code>symDecl</code> 
    * class symbol. */
  private def symDecl(sym: Symbol, name: String) = sym.tpe.decl(name)
  
  /** Retrieve the constructor Symbol for the passed <code>cs</code> class symbol. */
  private def constructorDecl(cs: ClassSymbol) = cs.tpe.decl(nme.CONSTRUCTOR)
  
  /** Module for creating scalac Tree nodes for calling methods of the 
   * <code>org.scalacheck.Gen</code> class and module.*/
  trait Gen {
  
    /** Symbol for the <code>org.scalacheck.Gen</code> module definition. */
    private lazy val moduleGenSym = definitions.getModule("org.scalacheck.Gen")
    
    /** Symbol for the <code>org.scalacheck.Gen</code> class definition. */
    private lazy val classGenSym = moduleGenSym.linkedClassOfModule                  
  
  
    /**
     * Apply <code>polyTpe</code> to the polymorphic type <code>org.scalacheck.Gen</code>.
     * 
     * @param polyTpe the type to be applied to <code>org.scalacheck.Gen</code>.
     * @return The polymorphic type resulting from applying <code>polyTpe</code> 
     *         to the polymorphic type <code>org.scalacheck.Gen</code>, i.e., 
     *         <code>Gen[polyTpe]</code>.
     */
    private def applyType(polyTpe: Type) = appliedType(classGenSym.tpe, List(polyTpe))
    
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.value[T](rhs)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def value(rhs: Tree): Tree =
      Apply(Select(Ident(moduleGenSym), symDecl(moduleGenSym, "value")), List(rhs))
    
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.oneOf[T](generators)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def oneOf(generators: List[Symbol]): Tree = 
      Apply(Select(Ident(moduleGenSym), symDecl(moduleGenSym, "oneOf")), generators.map(Ident(_)))
    
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.flatMap[T](body)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def flatMap(qualifier: Tree, body: Tree): Tree = 
      Apply(Select(qualifier, symDecl(classGenSym, "flatMap")),List(body))
     
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.map[T](rhs)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def map(qualifier: Tree, body: Tree): Tree = 
      Apply(Select(qualifier, symDecl(classGenSym, "map")), List(body))
     
    /**
     * Utilitary method for creating a method symbol for a <code>org.scalacheck.Gen</codee>
     * generator method. 
     * 
     * @param owner   The owner of the method (DefDef) which will use the returned method symbol.
     * @param genName The name of the method symbol (which will also be the name of the method).
     * @param retTpe  The method's returning type.
     * @return The method symbol for a generator method.
     */
    def createGenDefSymbol(owner: Symbol, genName: String, retTpe: Type): Symbol = {
      // returning type of the new method, i.e., Gen["retTpe"]
      val genDefRetTpe = applyType(retTpe)
      
      // create a symbol for the generator method that will be created next
      owner.newMethod(owner.pos,genName).setInfo(PolyType(List(), genDefRetTpe))
    }
    
    
    
   
    
//    def buildGenDefDef(cd: ClassDef, genDefSym: Symbol): DefDef = {
//      val constructorSym = constructorDecl(cd.symbol.asInstanceOf[ClassSymbol])
//      val paramss = constructorSym.typeParams
//       
//      assert(paramss.size <= 1, "currying is not supported. Change signature of "+constructorSym)
//      
//      
//      if(cd.symbol.hasFlag(scala.tools.nsc.symtab.Flags.ABSTRACT)) {
//        val generators = constructorSym.children.toList.map(s => genForTpe(s.tpe)).flatMap(v=>v)
//        DefDef(genDefSym, Modifiers(0), List(), Gen.oneOf(generators))
//      } 
//      else {
//        
//        val constrObj = resetAttrs(d.tpt.duplicate)
//        val instance = Select(New(constrObj), nme.CONSTRUCTOR)
//        
//        if(paramss.isEmpty) {
//          DefDef(genDefSym, Modifiers(0), List(), Gen.value(Apply(instance, Nil)))
//        } 
//        else {
//          //should use Tree.duplicate instead!!
//          val body = rhsGenDef(instance)(d)(genDef)
//        
//          DefDef(genDef, Modifiers(0), List(), body)
//        }
//      }
//    }
    
  }
  
  
  
  /** Module for creating scalac Tree nodes for calling methods of the 
   * <code>org.scalacheck.Arbitrary</code> class and module.*/
  trait Arbitrary {
   
    /** Symbol for the <code>org.scalacheck.Arbitrary</code> module definition. */
    private val moduleArbitrarySym = definitions.getModule("org.scalacheck.Arbitrary")
    
    /** Symbol for the <code>org.scalacheck.Arbitrary</code> class definition. */
    private val classArbitrarySym = moduleArbitrarySym.linkedClassOfModule 
    
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbInt</code> method definition. */
    private val arbInt          =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbInt"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbBool</code> method definition. */
    private val arbBool         =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbBool"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbLong</code> method definition. */
    private val arbLong         =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbLong"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbThrowable</code> method definition. */
    private val arbThrowable    =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbThrowable"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbDouble</code> method definition. */
    private val arbDouble       =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbDouble"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbChar</code> method definition. */
    private val arbChar         =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbChar"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbString</code> method definition. */
    private val arbString       =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbString"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbOption</code> method definition. */
    private val arbOption       =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbOption"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbImmutableMap</code> method definition. */
    private val arbImmutableMap =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbImmutableMap"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbList</code> method definition. */
    private val arbList         =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbList"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbSet</code> method definition. */
    private val arbSet          =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbSet"))
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbTuple2</code> method definition. */
    private val arbTuple2       =  Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbTuple2"))
    
    //[[TODO]]
    //lazy val arbMultiSet       =  Select(Ident(arbitraryModule), arbitraryModule.tpe.decl("arbMultiSet"))
    
    
    
    /** Map that stores <code>org.scalacheck.Arbitrary.arbitrary[Type]</code> calls. */
    protected val tpe2arbApp    = scala.collection.mutable.Map.empty[Type,Apply]
    
    // initialize map with ScalaCheck built-in types that are part of our PureScala language
    tpe2arbApp += definitions.IntClass.typeConstructor       -> applyArbitrary(arbInt)
    tpe2arbApp += definitions.BooleanClass.typeConstructor   -> applyArbitrary(arbBool)
    tpe2arbApp += definitions.LongClass.typeConstructor      -> applyArbitrary(arbLong)
    tpe2arbApp += definitions.ThrowableClass.typeConstructor -> applyArbitrary(arbThrowable)
    tpe2arbApp += definitions.DoubleClass.typeConstructor    -> applyArbitrary(arbDouble)
    tpe2arbApp += definitions.CharClass.typeConstructor      -> applyArbitrary(arbChar)
    tpe2arbApp += definitions.StringClass.typeConstructor    -> applyArbitrary(arbString)
    
    /**
     * Apply <code>polyTpe</code> to the polymorphic type <code>org.scalacheck.Arbitrary</code>.
     * 
     * @param polyTpe the type to be applied to <code>org.scalacheck.Arbitrary</code>.
     * @return The polymorphic type resulting from applying <code>polyTpe</code> 
     *         to the polymorphic type <code>org.scalacheck.Arbitrary</code>, i.e., 
     *         <code>Arbitrary[polyTpe]</code>.
     */
    private def applyType(tpe: Type) = appliedType(classArbitrarySym.tpe, List(tpe))
    
    /**
     * Creates a Tree node for the call <code>org.scalacheck.Arbitrary.apply[T](generator)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def apply(generator: Tree): Tree = 
      Apply(Select(Ident(moduleArbitrarySym),symDecl(moduleArbitrarySym, "apply")), List(generator))
    
    /**
     * 
     */
    def arbitrary(polyTpe: TypeTree): Apply = {
      val symbol = polyTpe.symbol
      val tpe = symbol.tpe
      tpe2arbApp.get(tpe) match {
        case Some(appliedArbitrary) => appliedArbitrary
        case None => arbitrary(symbol)
      }
    }
    
    protected def arbitrary(tpeSym: Symbol): Apply 
    
                                  
    protected def applyArbitrary(param: Tree): Apply =
      Apply(Select(Ident(moduleArbitrarySym), symDecl(moduleArbitrarySym, "arbitrary")), List(param))
    
    
    /**
     * Utilitary method for creating a method symbol for a <code>org.scalacheck.Arbitrary</codee>
     * generator method. 
     * 
     * @param owner   The owner of the method (DefDef) which will use the returned method symbol.
     * @param arbName The name of the method symbol (which will also be the name of the method).
     * @param retTpe  The method's returning type.
     * @return The method symbol for a generator method.
     */
    def createArbitraryDefSymbol(owner: Symbol, arbName: String, retTpe: Type): Symbol = {
      // returning type of the new method, i.e., Arbitrary["retTpe"]
      val arbRetTpe = applyType(retTpe)
      
      // Create the DefDef for the new Arbitrary object
      val arbDef = owner.newMethod(owner.pos, arbName).setInfo(PolyType(List(), arbRetTpe))
      // Implicit only because of ScalaCheck rational (not really needed since we are injecting code)
      arbDef.setFlag(scala.tools.nsc.symtab.Flags.IMPLICIT)
      
      arbDef
    }
  }
}
