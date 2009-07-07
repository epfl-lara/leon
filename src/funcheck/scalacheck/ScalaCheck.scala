package funcheck.scalacheck

import scala.tools.nsc.Global
import funcheck.util.FreshNameCreator

/**
 * Utilitarity class that is used as a factory for creating Tree nodes for method 
 * calls of classes and modules in the <code>org.scalacheck</code> package. 
 */
trait ScalaCheck extends FreshNameCreator {
  val global: Global
  import global._
  
    /** Transform the string <code>name</code> in method symbols from the <code>sym</code> 
     * class symbol. */
    private def symDecl(sym: Symbol, name: String) = sym.tpe.decl(name)
  
    /** Retrieve the constructor Symbol for the passed <code>cs</code> class symbol. */
    private def constructorDecl(cs: ClassSymbol) = cs.tpe.decl(nme.CONSTRUCTOR)
  
  trait GenericScalaCheckModule {
    protected val moduleSym: Symbol
    protected lazy val classSym = moduleSym.linkedClassOfModule
  
    
    protected def modDecl(method: String) = symDecl(moduleSym, method)
    protected def classDecl(method: String) = symDecl(classSym, method)
    
  
    protected def select(instance: Symbol, method: String): Select = 
      Select(Ident(instance), symDecl(instance,method))
    
    protected def apply(lhs: Tree, rhs: Tree): Apply = 
      apply(lhs, List(rhs))
    
    protected def apply(lhs: Tree, rhs: List[Tree]): Apply = 
      Apply(lhs, rhs)
  }
  
  
  /** Module for creating scalac Tree nodes for calling methods of the 
   * <code>org.scalacheck.Gen</code> class and module.*/
  object Gen extends GenericScalaCheckModule {
  
    /** Symbol for the <code>org.scalacheck.Gen</code> module definition. */
    override protected lazy val moduleSym = definitions.getModule("org.scalacheck.Gen")
    
    /**
     * Apply <code>polyTpe</code> to the polymorphic type <code>org.scalacheck.Gen</code>.
     * 
     * @param polyTpe the type to be applied to <code>org.scalacheck.Gen</code>.
     * @return The polymorphic type resulting from applying <code>polyTpe</code> 
     *         to the polymorphic type <code>org.scalacheck.Gen</code>, i.e., 
     *         <code>Gen[polyTpe]</code>.
     */
    private def applyType(polyTpe: Type) = appliedType(classSym.tpe, List(polyTpe))
    
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.value[T](rhs)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def value(rhs: Tree): Tree = apply(select(moduleSym, "value"), rhs)
    
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.oneOf[T](generators)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def oneOf(generators: List[Symbol]): Tree = 
      apply(select(moduleSym, "oneOf"), generators.map(Ident(_)))
    
    
    def lzy(generator: Tree): Tree = apply(select(moduleSym, "lzy"), generator)
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.flatMap[T](body)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def flatMap(qualifier: Tree, body: Tree): Tree = 
      apply(Select(qualifier, classDecl("flatMap")), body)
     
    
    /**
     * This creates a Tree node for the call <code>org.scalacheck.Gen.map[T](rhs)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def map(qualifier: Tree, body: Tree): Tree = 
      apply(Select(qualifier, classDecl("map")), body)
     
    
    
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
    
    
    
     /** 
     * Map that stores for each @generator annotated ClassDef or DefDef the automatically  
     * generated DefDef for creating instances of the <code>org.scalacheck.Gen</code> class.
     * The <code>Type</code> that is associated to the DefDef is either the type of the 
     * ClassDef or the returning type of the DefDef.
     */
    private val tpe2listGen = scala.collection.mutable.Map.empty[Type, List[DefDef]]
    private val tpe2listGenSym = scala.collection.mutable.Map.empty[Type, List[Symbol]]
    
     /** 
     * Add the <code>gen</code> generator DefDef declaration to the list of 
     * generators for <code>tpe</code>.
     * 
     * @param tpe The type of elements generated by the <code>gen</code>.
     * @param gen The DefDef declaration for the generator method.
     */
    def +[T](map: collection.mutable.Map[Type, List[T]], key: Type, value: T): Unit = map.get(key) match {
      case None         => map += key -> List(value)
      case Some(values) => map += key -> (value :: values)
    }
   
    /** List of generator DefDef symbols for a given type <code>tpe</code>*/
    def genSymbolsForType(tpe: Type): List[Symbol] = tpe2listGenSym.get(tpe) match {
      case None => Nil
      case Some(symbols) => symbols
    } 
    
    /** 
     * Second Pass: Create symbols for the generator DefDef that will be created
     * durind the Third Pass.
     */
    def createGenDefDef(klasses: List[ClassDef], defs: List[DefDef]): List[DefDef] = {
      val generable: List[(Symbol,Tree)] = createGenDefSyms(klasses, defs)
      
      for { (genSym, genTree) <- generable } genTree match {
        case cd: ClassDef => 
          val tpe = cd.symbol.tpe
          Gen + (tpe2listGen, tpe, Gen.createGenDef(cd, genSym))
        
        case d: DefDef =>
          val tpe = d.tpt.symbol.tpe
          val generated = DefDef(genSym, Modifiers(0), List(), rhsGenDef(Ident(d.name))(d)(genSym))
          Gen + (tpe2listGen, tpe, generated)
      }
      
      // flatten into single list values of Gen.tpe2listGen
      (List[DefDef]() /: Gen.tpe2listGen.values) {
        case (xs, xss) => xs ::: xss
      }
    }
    
    
    /** 
     * Create method symbols for each <code>@generator</code> annotated ClassDef
     * and DefDef.
     */
    private def createGenDefSyms(klasses: List[ClassDef], defs: List[DefDef]): List[(Symbol, Tree)] = {
    
      val genKlasses: List[(Symbol, ClassDef)] = for(klass <- klasses) yield {
        val genName = fresh.newName("gen"+klass.name)
        val tpe = klass.symbol.tpe
        val genSym = createGenDefSymbol(klass.symbol.enclClass.owner, genName, tpe)
        
        Gen + (tpe2listGenSym, tpe, genSym)
        
        (genSym, klass)
      }
    
      val genDefs: List[(Symbol, DefDef)] = for(d <- defs) yield {
        val genName = fresh.newName("gen"+d.name)
        val tpe = d.tpt.symbol.tpe
        val genSym = createGenDefSymbol(d.symbol.owner, genName, tpe)
        
        Gen + (tpe2listGenSym, tpe, genSym)
        
        (genSym, d)
      }
    
      genKlasses ::: genDefs
    }
    
    
    
    def createGenDef(cd: ClassDef, genDef: Symbol): DefDef = {
      val d: DefDef = getConstructorOf(cd)
      val DefDef(_,_,_,vparamss,retTpe,_) = d 
      assert(vparamss.size <= 1, "currying is not supported. Change signature of "+cd.symbol)
      
      
      if(cd.symbol.hasFlag(scala.tools.nsc.symtab.Flags.ABSTRACT)) {
        val generators = retTpe.symbol.children.toList.map(s => genSymbolsForType(s.tpe)).flatMap(v=>v)
        DefDef(genDef, Modifiers(0), List(), Gen.lzy(Gen.oneOf(generators)))
      } 
      else {
        
        val constrObj = resetAttrs(d.tpt.duplicate)
        val instance = Select(New(constrObj), nme.CONSTRUCTOR)
        
        assert(d.tpt.isInstanceOf[TypeTree])
        
        val body = rhsGenDef(instance)(d)(genDef)
        DefDef(genDef, Modifiers(0), List(), body)
      }
    }
    
    
     /** <code>base</code> is either 
     *       - Select(New(tpe),constructor) [constructor] 
     *       - Ident(name)   [method call]
     */
    private def rhsGenDef(base: Tree)(d: DefDef)(extOwner: Symbol): Tree = {
      val DefDef(_,name,_,vparamss,retTpe,_) = d
      assert(vparamss.size <= 1, "currying is not supported. Change signature of "+d.symbol)
      
      if(vparamss.head.isEmpty)
        Gen.value(Apply(base, Nil))
      
      else {
        var owner = extOwner
      
        val paramssTpe: List[ValDef] = vparamss.flatMap(v=>v).map(p => 
          ValDef(Modifiers(0), fresh.newName("v"), resetAttrs(p.tpt.duplicate), EmptyTree))
      
      
        var last = true
      
      
        val z :Tree = Apply(base, paramssTpe.map(p => Ident(p.name)))
        val body = (paramssTpe :\ z) {
          case (param,apply) => {
            val body = Function(List(param), apply)
            body.symbol.owner = owner
            owner = body.symbol
            //XXX: it is not flatMap in general. fix this!!
            if(last) {
              last = false
              Gen.map(Arbitrary.arbitrary(param.tpt.asInstanceOf[TypeTree]), body)
            } else
              Gen.flatMap(Arbitrary.arbitrary(param.tpt.asInstanceOf[TypeTree]), body)
          }
        }
      
        Gen.lzy(body)
      }
    }
   
    
    
    private def getConstructorOf(cd: ClassDef): DefDef = {
      val Template(parents, self, body) = cd.impl
      var dd: DefDef  = null
      for { b <- body } b match {
        case d @ DefDef(_, nme.CONSTRUCTOR, _, _, _, _) => dd = d
        case _ => ;
      }
      dd
    } ensuring (res => res != null)

  
    
  }
  
  
  
  /** Module for creating scalac Tree nodes for calling methods of the 
   * <code>org.scalacheck.Arbitrary</code> class and module.*/
  object Arbitrary extends GenericScalaCheckModule {
    
    
    /** Symbol for the <code>org.scalacheck.Arbitrary</code> module definition. */
    override protected lazy val moduleSym = definitions.getModule("org.scalacheck.Arbitrary")
    
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbInt</code> method definition. */
    private val arbInt          =  select(moduleSym, "arbInt")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbBool</code> method definition. */
    private val arbBool         =  select(moduleSym, "arbBool")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbLong</code> method definition. */
    private val arbLong         =  select(moduleSym, "arbLong")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbThrowable</code> method definition. */
    private val arbThrowable    =  select(moduleSym, "arbThrowable")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbDouble</code> method definition. */
    private val arbDouble       =  select(moduleSym, "arbDouble")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbChar</code> method definition. */
    private val arbChar         =  select(moduleSym, "arbChar")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbString</code> method definition. */
    private val arbString       =  select(moduleSym, "arbString")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbOption</code> method definition. */
    private val arbOption       =  select(moduleSym, "arbOption")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbImmutableMap</code> method definition. */
    private val arbImmutableMap =  select(moduleSym, "arbImmutableMap")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbList</code> method definition. */
    private val arbList         =  select(moduleSym, "arbList")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbSet</code> method definition. */
    private val arbSet          =  select(moduleSym, "arbSet")
    /** Symbol for the <code>org.scalacheck.Arbitrary.arbTuple2</code> method definition. */
    private val arbTuple2       =  select(moduleSym, "arbTuple2")
    
    //[[TODO]]
    //lazy val arbMultiSet       =  Select(Ident(arbitraryModule), arbitraryModule.tpe.decl("arbMultiSet"))
    
    
    
    /** Map that stores <code>org.scalacheck.Arbitrary.arbitrary[Type]</code> calls. */
    protected val tpe2arbApp    = scala.collection.mutable.Map.empty[Type,Tree]
    
    
    // initialize map with ScalaCheck built-in types that are part of our PureScala language
    import definitions._
    tpe2arbApp += IntClass.typeConstructor       -> arbInt
    tpe2arbApp += BooleanClass.typeConstructor   -> arbBool
    tpe2arbApp += LongClass.typeConstructor      -> arbLong
    tpe2arbApp += ThrowableClass.typeConstructor -> arbThrowable
    tpe2arbApp += DoubleClass.typeConstructor    -> arbDouble
    tpe2arbApp += CharClass.typeConstructor      -> arbChar
    tpe2arbApp += StringClass.typeConstructor    -> arbString
    tpe2arbApp += OptionClass.typeConstructor    -> arbOption
    
    lazy val ImmutableMapClass: Symbol = getClass("scala.collection.immutable.Map")
    lazy val ImmutableSetClass: Symbol = getClass("scala.collection.immutable.Set")
    
    tpe2arbApp += ImmutableMapClass.typeConstructor    -> arbImmutableMap
    tpe2arbApp += ListClass.typeConstructor            -> arbList
    tpe2arbApp += ImmutableSetClass.typeConstructor    -> arbSet
    tpe2arbApp += TupleClass(2).typeConstructor        -> arbTuple2 
    
    /**
     * Apply <code>polyTpe</code> to the polymorphic type <code>org.scalacheck.Arbitrary</code>.
     * 
     * @param polyTpe the type to be applied to <code>org.scalacheck.Arbitrary</code>.
     * @return The polymorphic type resulting from applying <code>polyTpe</code> 
     *         to the polymorphic type <code>org.scalacheck.Arbitrary</code>, i.e., 
     *         <code>Arbitrary[polyTpe]</code>.
     */
    private def applyType(tpe: Type) = appliedType(classSym.tpe, List(tpe))
    
    /**
     * Creates a Tree node for the call <code>org.scalacheck.Arbitrary.apply[T](generator)</code>, 
     * where the polymorphic type <code>T</code> will be inferred during the next 
     * typer phase (this usually means that the typer has to be called explictly, 
     * so it is the developer duty to ensure that this happen at some point).
     */
    def apply(generator: Tree): Tree = apply(select(moduleSym, "apply"), generator)
    
    def arbitrary(tpe: Type): Tree = tpe match {
      //case TypeRef(_,sym,List(p)) if p.prefix == NoPrefix => tpe2arbApp.get(tpe).get
      case TypeRef(_,sym,List(p)) => apply(arbitrary(sym.typeConstructor), arbitrary(p))
      case tpe => tpe2arbApp.get(tpe).get
    }
    
    /**
     * 
     */
    def arbitrary(polyTpe: TypeTree): Apply = {
      val symbol = polyTpe.symbol
      val tpe = symbol.tpe
      tpe2arbApp.get(tpe) match {
        case Some(arb) => applyArbitrary(arb)
        case None => arbitrary(symbol)
      }
    }
    
    /** Map that stores not built-in <code>org.scalacheck.Arbitrary</code> DefDef definitions. */
    private val tpe2arbDefDef = scala.collection.mutable.Map.empty[Type,DefDef]
    
    def getArbitraryDefDefs: List[DefDef] = tpe2arbDefDef.values.toList
    
    def arbitrary(tpeSym: Symbol): Apply = {
      require(tpe2arbApp.get(tpeSym.tpe).isEmpty, "Arbitrary.arbitrary["+tpeSym.tpe+"] is already in the map")
      
      val owner = tpeSym.toplevelClass
      val arbName = fresh.newName("arb"+tpeSym.name)
      val tpe = tpeSym.tpe
      
      val arbDef = createArbitraryDefSymbol(owner, arbName, tpe)
      
            
      val genNames = Gen.genSymbolsForType(tpe)
      
      
      val generated = DefDef(arbDef, Modifiers(0), List(), Arbitrary(Gen.oneOf(genNames)))
      tpe2arbDefDef += tpe -> generated  
      
      val result = applyArbitrary(Ident(arbDef))
      tpe2arbApp += tpe -> Ident(arbDef)
        
      result
            
    }
    
                                  
    protected def applyArbitrary(param: Tree): Apply = 
      apply(select(moduleSym, "arbitrary"), param)
    
    
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
  
  object Prop {
    
    private lazy val modulePropSym: Symbol = definitions.getModule("org.scalacheck.Prop")
    
    /** Transform string name in method symbols from the <code>symDecl</code> 
     * class symbol. 
     */
    private def decl(name: String) = modulePropSym.tpe.decl(name)
    
    private def moduleApply(method: String, args: List[Tree]): Apply = 
      Apply(Select(Ident(modulePropSym), decl(method)), args)
    
    def forAll(props: List[Tree]): Apply = 
      moduleApply("forAll", props)
    
    def forAll(prop: Tree): Apply = forAll(List(prop))
    
    def ==>(ifz: Tree, then: Tree): Apply = moduleApply("==>", List(ifz,propBoolean(then)))
    
    def propBoolean(prop: Tree): Apply = moduleApply("propBoolean", List(prop))
  }
  
  
  object Shrink {
    private def select(instance: Symbol, method: String): Select = 
      Select(Ident(instance), symDecl(instance,method))
    
    /** Symbol for the <code>org.scalacheck.Shrink</code> module definition. */
    private val moduleShrinkSym = definitions.getModule("org.scalacheck.Shrink")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkInt</code> method definition. */
    private val shrinkInt          =  select(moduleShrinkSym, "shrinkInt")    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkString</code> method definition. */
    private val shrinkString       =  select(moduleShrinkSym, "shrinkString")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkOption</code> method definition. */
    private val shrinkOption       =  select(moduleShrinkSym, "shrinkOption")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkList</code> method definition. */
    private val shrinkList         =  select(moduleShrinkSym, "shrinkList")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkSet</code> method definition. */
    private val shrinkSet          =  select(moduleShrinkSym, "shrinkSet")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple2</code> method definition. */
    private val shrinkTuple2       =  select(moduleShrinkSym, "shrinkTuple2")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple3</code> method definition. */
    private val shrinkTuple3       =  select(moduleShrinkSym, "shrinkTuple3")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple4</code> method definition. */
    private val shrinkTuple4       =  select(moduleShrinkSym, "shrinkTuple4")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple5</code> method definition. */
    private val shrinkTuple5       =  select(moduleShrinkSym, "shrinkTuple5")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple6</code> method definition. */
    private val shrinkTuple6       =  select(moduleShrinkSym, "shrinkTuple6")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple7</code> method definition. */
    private val shrinkTuple7       =  select(moduleShrinkSym, "shrinkTuple7")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple8</code> method definition. */
    private val shrinkTuple8       =  select(moduleShrinkSym, "shrinkTuple8")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkTuple9</code> method definition. */
    private val shrinkTuple9       =  select(moduleShrinkSym, "shrinkTuple9")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkIntList</code> method definition. */
    private val shrinkIntList      =  select(moduleShrinkSym, "shrinkIntList")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkBooleanList</code> method definition. */
    private val shrinkBooleanList  =  select(moduleShrinkSym, "shrinkBooleanList")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkDoubleList</code> method definition. */
    private val shrinkDoubleList   =  select(moduleShrinkSym, "shrinkDoubleList")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkStringList</code> method definition. */
    private val shrinkStringList   =  select(moduleShrinkSym, "shrinkStringList")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkIntSet</code> method definition. */
    private val shrinkIntSet       =  select(moduleShrinkSym, "shrinkIntSet")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkBooleanSet</code> method definition. */
    private val shrinkBooleanSet   =  select(moduleShrinkSym, "shrinkBooleanSet")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkDoubleSet</code> method definition. */
    private val shrinkDoubleSet    =  select(moduleShrinkSym, "shrinkDoubleSet")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkStringSet</code> method definition. */
    private val shrinkStringSet    =  select(moduleShrinkSym, "shrinkStringSet")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkIntOption</code> method definition. */
    private val shrinkIntOption    =  select(moduleShrinkSym, "shrinkIntOption")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkBooleanOption</code> method definition. */
    private val shrinkBooleanOption=  select(moduleShrinkSym, "shrinkBooleanOption")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkDoubleOption</code> method definition. */
    private val shrinkDoubleOption =  select(moduleShrinkSym, "shrinkDoubleOption")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkStringOption</code> method definition. */
    private val shrinkStringOption =  select(moduleShrinkSym, "shrinkStringOption")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkIntTuple2</code> method definition. */
    private val shrinkIntTuple2    =  select(moduleShrinkSym, "shrinkIntTuple2")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkBooleanTuple2</code> method definition. */
    private val shrinkBooleanTuple2=  select(moduleShrinkSym, "shrinkBooleanTuple2")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkDoubleTuple2</code> method definition. */
    private val shrinkDoubleTuple2 =  select(moduleShrinkSym, "shrinkDoubleTuple2")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkStringTuple2</code> method definition. */
    private val shrinkStringTuple2 =  select(moduleShrinkSym, "shrinkStringTuple2")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkIntTuple3</code> method definition. */
    private val shrinkIntTuple3    =  select(moduleShrinkSym, "shrinkIntTuple3")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkBooleanTuple3</code> method definition. */
    private val shrinkBooleanTuple3=  select(moduleShrinkSym, "shrinkBooleanTuple3")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkDoubleTuple3</code> method definition. */
    private val shrinkDoubleTuple3 =  select(moduleShrinkSym, "shrinkDoubleTuple3")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkStringTuple3</code> method definition. */
    private val shrinkStringTuple3 =  select(moduleShrinkSym, "shrinkStringTuple3")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkIntTuple4</code> method definition. */
    private val shrinkIntTuple4    =  select(moduleShrinkSym, "shrinkIntTuple4")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkBooleanTuple4</code> method definition. */
    private val shrinkBooleanTuple4=  select(moduleShrinkSym, "shrinkBooleanTuple4")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkDoubleTuple4</code> method definition. */
    private val shrinkDoubleTuple4 =  select(moduleShrinkSym, "shrinkDoubleTuple4")
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkStringTuple4</code> method definition. */
    private val shrinkStringTuple4 =  select(moduleShrinkSym, "shrinkStringTuple4")
    
    /** Symbol for the <code>org.scalacheck.Shrink.shrinkAny</code> method definition.
     *  This is a generic shrinker which does not shrink whatever object is passed to it.
     */
    private val shrinkAny          =  select(moduleShrinkSym, "shrinkAny")
    
    def shrinker(tpe: Type): Select = tpe2shrinker.getOrElse(tpe, shrinkAny)
    
    private val tpe2shrinker: Map[Type, Select] = {
      import definitions._
      val SetClass: Symbol = definitions.getClass("scala.collection.immutable.Set")
      
      def apply(container: Type)(parametric: Type): Type = 
        appliedType(container, List(parametric))
        
      def listOf(tpe: Type): Type = apply(ListClass.typeConstructor)(tpe) 
      def setOf(tpe: Type): Type = apply(SetClass.typeConstructor)(tpe)
      def optionOf(tpe: Type): Type = apply(OptionClass.typeConstructor)(tpe)
      def tupleOf(arity: Int, tpe: Type): Type = apply(TupleClass(arity).typeConstructor)(tpe)
      
      val IntListTpe     = listOf(IntClass.typeConstructor)
      val BooleanListTpe = listOf(BooleanClass.typeConstructor)
      val DoubleListTpe  = listOf(DoubleClass.typeConstructor)
      val StringListTpe  = listOf(StringClass.typeConstructor)
      
      val IntSetTpe      = setOf(IntClass.typeConstructor)
      val BooleanSetTpe  = setOf(BooleanClass.typeConstructor)
      val DoubleSetTpe   = setOf(DoubleClass.typeConstructor)
      val StringSetTpe   = setOf(StringClass.typeConstructor)
      
      val IntOptionTpe     = optionOf(IntClass.typeConstructor)
      val BooleanOptionTpe = optionOf(BooleanClass.typeConstructor)
      val DoubleOptionTpe  = optionOf(DoubleClass.typeConstructor)
      val StringOptionTpe  = optionOf(StringClass.typeConstructor)
      
      val IntTuple2Tpe     = tupleOf(2, IntClass.typeConstructor)
      val BooleanTuple2Tpe = tupleOf(2, BooleanClass.typeConstructor)
      val DoubleTuple2Tpe  = tupleOf(2, DoubleClass.typeConstructor)
      val StringTuple2Tpe  = tupleOf(2, StringClass.typeConstructor)
      
      val IntTuple3Tpe     = tupleOf(3, IntClass.typeConstructor)
      val BooleanTuple3Tpe = tupleOf(3, BooleanClass.typeConstructor)
      val DoubleTuple3Tpe  = tupleOf(3, DoubleClass.typeConstructor)
      val StringTuple3Tpe  = tupleOf(3, StringClass.typeConstructor)
      
      val IntTuple4Tpe     = tupleOf(4, IntClass.typeConstructor)
      val BooleanTuple4Tpe = tupleOf(4, BooleanClass.typeConstructor)
      val DoubleTuple4Tpe  = tupleOf(4, DoubleClass.typeConstructor)
      val StringTuple4Tpe  = tupleOf(4, StringClass.typeConstructor)
      
      Map(IntClass.typeConstructor -> shrinkInt,
          StringClass.typeConstructor     -> shrinkString, 
          OptionClass.typeConstructor     -> shrinkOption,
          ListClass.typeConstructor       -> shrinkList,
          SetClass.typeConstructor        -> shrinkSet,
          TupleClass(2).typeConstructor   -> shrinkTuple2,
          TupleClass(3).typeConstructor   -> shrinkTuple3,
          TupleClass(4).typeConstructor   -> shrinkTuple4,
          TupleClass(5).typeConstructor   -> shrinkTuple5,
          TupleClass(6).typeConstructor   -> shrinkTuple6,
          TupleClass(7).typeConstructor   -> shrinkTuple7,
          TupleClass(8).typeConstructor   -> shrinkTuple8,
          TupleClass(9).typeConstructor   -> shrinkTuple9,
          IntListTpe                      -> shrinkIntList,
          BooleanListTpe                  -> shrinkBooleanList,
          DoubleListTpe                   -> shrinkDoubleList,
          StringListTpe                   -> shrinkStringList,
          IntSetTpe                       -> shrinkIntSet,
          BooleanSetTpe                   -> shrinkBooleanSet,
          DoubleSetTpe                    -> shrinkDoubleSet,
          StringSetTpe                    -> shrinkStringSet,
          IntOptionTpe                    -> shrinkIntOption,
          BooleanOptionTpe                -> shrinkBooleanOption,
          DoubleOptionTpe                 -> shrinkDoubleOption,
          StringOptionTpe                 -> shrinkStringOption,
          IntTuple2Tpe                    -> shrinkIntTuple2,
          BooleanTuple2Tpe                -> shrinkBooleanTuple2,
          DoubleTuple2Tpe                 -> shrinkDoubleTuple2,
          StringTuple2Tpe                 -> shrinkStringTuple2,
          IntTuple3Tpe                    -> shrinkIntTuple3,
          BooleanTuple3Tpe                -> shrinkBooleanTuple3,
          DoubleTuple3Tpe                 -> shrinkDoubleTuple3,
          StringTuple3Tpe                 -> shrinkStringTuple3,
          IntTuple4Tpe                    -> shrinkIntTuple4,
          BooleanTuple4Tpe                -> shrinkBooleanTuple4,
          DoubleTuple4Tpe                 -> shrinkDoubleTuple4,
          StringTuple4Tpe                 -> shrinkStringTuple4
      )
    }
  }
  
  
  object ConsoleReporter {
    /** Symbol for the <code>org.scalacheck.ConsoleReporter</code> module definition. */
    private val moduleConsoleReporterSym = definitions.getModule("org.scalacheck.ConsoleReporter")
    
    def testStatsEx(testRes: Tree): Tree = testStatsEx("", testRes)
                                                       
    def testStatsEx(msg: String, testRes: Tree): Tree = 
      Apply(Select(Ident(moduleConsoleReporterSym), symDecl(moduleConsoleReporterSym, "testStatsEx")), List(Literal(msg), testRes))
  }
  
  object Test {
    /** Symbol for the <code>org.scalacheck.Test</code> module definition. */
    private val moduleTestSym = definitions.getModule("org.scalacheck.Test")
    
    def check(prop: Tree): Tree = 
      Apply(Select(Ident(moduleTestSym), symDecl(moduleTestSym, "check")), List(prop))
  }
}
