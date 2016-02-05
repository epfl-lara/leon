package leon
package solvers
package z3

import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Types._
import purescala.Definitions._
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.interpreters.Z3Interpreter
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}
import _root_.smtlib.theories.ArraysEx
import leon.utils.Bijection

object Z3StringTypeConversion {
  def convert(t: TypeTree)(implicit p: Program) = new Z3StringTypeConversion { def getProgram = p }.convertType(t)
  def convertToString(e: Expr)(implicit p: Program) = new Z3StringTypeConversion{ def getProgram = p }.convertToString(e)
}

trait Z3StringTypeConversion {
  val stringBijection = new Bijection[String, Expr]()
  
  lazy val conschar = program.lookupCaseClass("leon.collection.Cons") match {
    case Some(cc) => cc.typed(Seq(CharType))
    case _ => throw new Exception("Could not find Cons in Z3 solver")
  }
  lazy val nilchar = program.lookupCaseClass("leon.collection.Nil") match {
    case Some(cc) => cc.typed(Seq(CharType))
    case _ => throw new Exception("Could not find Nil in Z3 solver")
  }
  lazy val listchar = program.lookupAbstractClass("leon.collection.List") match {
    case Some(cc) => cc.typed(Seq(CharType))
    case _ => throw new Exception("Could not find List in Z3 solver")
  }
  def lookupFunDef(s: String): FunDef = program.lookupFunDef(s) match {
    case Some(fd) => fd
    case _ => throw new Exception("Could not find function "+s+" in program")
  }
  lazy val list_size = lookupFunDef("leon.collection.List.size").typed(Seq(CharType))
  lazy val list_++ = lookupFunDef("leon.collection.List.++").typed(Seq(CharType))
  lazy val list_take = lookupFunDef("leon.collection.List.take").typed(Seq(CharType))
  lazy val list_drop = lookupFunDef("leon.collection.List.drop").typed(Seq(CharType))
  lazy val list_slice = lookupFunDef("leon.collection.List.slice").typed(Seq(CharType))
  
  private lazy val program = getProgram
  
  def getProgram: Program
  
  def convertType(t: TypeTree): TypeTree = t match {
    case StringType => listchar
    case _ => t
  }
  def convertToString(e: Expr)(implicit p: Program): String  = 
    stringBijection.cachedA(e) {
      e match {
        case CaseClass(_, Seq(CharLiteral(c), l)) => c + convertToString(l)
        case CaseClass(_, Seq()) => ""
      }
    }
  def convertFromString(v: String) =
    stringBijection.cachedB(v) {
      v.toList.foldRight(CaseClass(nilchar, Seq())){
        case (char, l) => CaseClass(conschar, Seq(CharLiteral(char), l))
      }
    }
}

trait Z3StringConversion[TargetType] extends Z3StringTypeConversion {
  def convertToTarget(e: Expr)(implicit bindings: Map[Identifier, TargetType]): TargetType
  def targetApplication(fd: TypedFunDef, args: Seq[TargetType])(implicit bindings: Map[Identifier, TargetType]): TargetType
  
  object StringConverted {
    def unapply(e: Expr)(implicit bindings: Map[Identifier, TargetType]): Option[TargetType] = e match {
      case StringLiteral(v)          =>
        // No string support for z3 at this moment.
        val stringEncoding = convertFromString(v)
        Some(convertToTarget(stringEncoding))
      case StringLength(a)           =>
        Some(targetApplication(list_size, Seq(convertToTarget(a))))
      case StringConcat(a, b)        =>
        Some(targetApplication(list_++, Seq(convertToTarget(a), convertToTarget(b))))
      case SubString(a, start, Plus(start2, length)) if start == start2  =>
        Some(targetApplication(list_take,
            Seq(targetApplication(list_drop, Seq(convertToTarget(a), convertToTarget(start))), convertToTarget(length))))
      case SubString(a, start, end)  => 
        Some(targetApplication(list_slice, Seq(convertToTarget(a), convertToTarget(start), convertToTarget(end))))
      case _ => None
    }
    
    def apply(t: TypeTree): TypeTree = convertType(t)
  }
}