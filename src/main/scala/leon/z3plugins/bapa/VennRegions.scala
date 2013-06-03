/* Copyright 2009-2013 EPFL, Lausanne */

package purescala.z3plugins.bapa

import scala.collection.mutable.{ArrayBuffer,HashMap}
import z3.scala.{Z3Context, Z3AST, Z3Theory}
import AST._

import scala.sys.error

trait VennRegions {
  val z3: Z3Context
  protected def assertAxiomSafe(ast: Z3AST): Unit

  case class SetName(name: String, sym: Symbol) {
    def complName = name.toLowerCase
    override def toString = name
  }
 
  case class VennRegion(name: String, ast: Z3AST) {
    def toTree = Var(IntSymbol(ast))
    override def toString = name
  }

  /* Cache */
  
  private val cachedNames = new HashMap[Symbol, SetName]
  private val cachedRegions = new HashMap[String, VennRegion]
  private var namesCounter = 0
  private val mkZero = z3.mkInt(0, z3.mkIntSort)
  
  private def mkName(sym: Symbol) = {
    cachedNames getOrElse (sym, {
      val name = SetName(('A' + namesCounter).toChar.toString, sym)
      namesCounter += 1
      cachedNames(sym) = name
//       println("*** New Set :  " + sym + " -> '" + name + "' ***")
      name
    })
  }
  
  private def mkRegion(sets: Seq[SetName], region: Long) = {
    val names = for (i <- 0 until sets.size) yield
      if ((region & (1 << i)) != 0) sets(i).name
      else sets(i).complName
    val name = (names sortWith {_.toLowerCase < _.toLowerCase}).mkString
    cachedRegions getOrElse(name, {
      val region = VennRegion(name, z3.mkFreshConst(name, z3.mkIntSort))
      cachedRegions(name) = region
      region
    })
  }

  /* Venn region bookkeeping */

  sealed abstract class Universe {
    val setVariables: Seq[SetName]
    val vennRegions: Array[VennRegion]
    
    def variables = setVariables map {_.sym}
    
    def addSet(symbol: Symbol) = {
      val name = mkName(symbol)
      if (setVariables contains name) {
        this
      } else {
//         println("Adding set: " + symbol)
//         println("AKA       : " + name)
        new ExtendedUniverse(name, this)
      }
    }
    
    def addSets(symbols: Iterable[Symbol]) = {
      var universe = this 
      for (sym <- symbols) universe = universe addSet sym
      universe
    }
    
    def translate(tree: Tree): Tree = {
      val regions = translate0(tree).toSeq.sortWith{_ < _} map {i => vennRegions(i).toTree}
      if (regions.size > 0) Op(ADD, regions) else 0
    }
    
    private def translate0(tree: Tree): Set[Int] = tree match {
      case Lit(EmptySetLit) =>
        Set.empty
      case Op(COMPL, Seq(Lit(EmptySetLit))) =>
        val regions = new scala.collection.mutable.HashSet[Int]
        for (i <- 0 until vennRegions.size)
          regions += i
        regions.toSet
      case Var(sym) =>
        if (sym.typ != SetType) error("Not a set variable : " + sym)
        val setNum = setVariables indexOf mkName(sym)
        if (setNum == -1) error("Unknown set in this universe : " + sym)
        val regions = new scala.collection.mutable.HashSet[Int]
        for (i <- 0 until vennRegions.size; if (i & (1 << setNum)) != 0)
          regions += i
        regions.toSet
      case Op(COMPL, Seq(Var(sym))) =>
        if (sym.typ != SetType) error("Not a set variable : " + sym)
        val setNum = setVariables indexOf mkName(sym)
        val regions = new scala.collection.mutable.HashSet[Int]
        for (i <- 0 until vennRegions.size; if (i & (1 << setNum)) == 0)
          regions += i
        regions.toSet
      case Op(UNION, ts) =>
        ts map translate0 reduceLeft {_ ++ _}
      case Op(INTER, ts) =>
        ts map translate0 reduceLeft {_ & _}
      case _ =>
        error("Not a simplified set expression : " + tree)
    }

    def assertAllAxioms: Unit
  }

  class EmptyUniverse(val domainSize: Z3AST) extends Universe {
    val setVariables = Nil
    val vennRegions = Array(VennRegion("UnivRegion", domainSize))
    def assertAllAxioms { }
  }

  class ExtendedUniverse(setVar: SetName, val parent: Universe) extends Universe {
    val setVariables = parent.setVariables :+ setVar
    val (vennRegions, axioms) = {
      if (setVariables.size > 16) {
        println("WARNING: Creating venn regions for more than 16 set variables (" + setVariables.size + " variables).")
//         error("More than 16 set variables")
      }
      val n = parent.vennRegions.size
      val _vennRegions = new Array[VennRegion](2 * n)
      val _axioms = new ArrayBuffer[Z3AST](3 * n)
      
      for (i <- 0 until n) {
        val old = parent.vennRegions(i)
        val vr1 = mkRegion(setVariables, i)
        val vr2 = mkRegion(setVariables, i + n)
        _vennRegions(i) = vr1
        _vennRegions(i + n) = vr2
        _axioms += z3.mkEq(old.ast, z3.mkAdd(vr1.ast, vr2.ast))
        _axioms += z3.mkGE(vr1.ast, mkZero)
        _axioms += z3.mkGE(vr2.ast, mkZero)
//         val axiom = z3.mkAnd(axiom1, axiom2, axiom3)
//         assertAxiom(axiom)
//         println(axiom)
//         assertAxiomEventually(axiom1)
//         assertAxiomEventually(axiom2)
//         assertAxiomEventually(axiom3)
//         println(axiom1)
//         println(axiom2)
//         println(axiom3)
//         println("*** " + old.ast + " := " + vr1.ast + " + " + vr2.ast)
      }
      (_vennRegions, _axioms.toArray)
    }
    assertAllAxioms

    def assertAllAxioms {
      parent.assertAllAxioms
      axioms foreach assertAxiomSafe
    }
    /*
    // (Ab = 0 & aB = 0) <=> A = B
    {
      val a = Var(setVar.sym)
      for (oldSetVar <- parent.setVariables) {
        val b = Var(oldSetVar.sym)
//         println("******** LOOOL : " + (a seteq b))
        val tree = (
         (translate(a ** ~b) === 0) &&
         (translate(~a ** b) === 0)
        ) iff (a seteq b)
        assertAxiomEventually(tree)
      }
    }
    */
  }
}


