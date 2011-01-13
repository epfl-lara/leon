package purescala.z3plugins.instantiator

import z3.scala._
import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import purescala.Z3Solver

trait AbstractInstantiator {
  val z3Solver : Z3Solver
  def isKnownDef(funDef: FunDef) : Boolean
  def functionDefToDecl(funDef: FunDef) : Z3FuncDecl
  def isKnownDecl(decl: Z3FuncDecl) : Boolean
  def functionDeclToDef(decl: Z3FuncDecl) : FunDef
  protected[purescala] def registerFunction(funDef: FunDef, sorts: Seq[Z3Sort], returnSort: Z3Sort) : Unit 
  def possibleContinuation : Boolean
  def increaseSearchDepth() : Unit
  def dumpFunctionMap : Unit
}
