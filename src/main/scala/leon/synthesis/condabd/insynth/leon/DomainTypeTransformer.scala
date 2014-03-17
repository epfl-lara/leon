/* Copyright 2009-2014 EPFL, Lausanne */

package leon.synthesis.condabd.insynth.leon

import insynth.structures._

import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions._

import scala.language.implicitConversions

object DomainTypeTransformer extends ( LeonType => DomainType ) {
  
  val InSynthTypeTransformer = TypeTransformer
  
  def apply(typeDef: ClassDef): DomainType = {    		
		implicit def singletonList(x: DomainType) = List(x)

    typeDef match {
      case abs: AbstractClassDef => Atom(Const(abs.id.name))
      case caseClassDef: CaseClassDef => Atom(Const(caseClassDef.id.name))
    }
  }
	
  def apply(leonType: LeonType): DomainType = {    		
		implicit def singletonList(x: DomainType) = List(x)

    leonType match {
      case Untyped => throw new RuntimeException("Should not happen at this point")
      case BooleanType => Atom(Const("Boolean"))
      case UnitType => Atom(Const("Unit"))
      case Int32Type => Atom(Const("Int"))
      case TypeParameter(id) => Atom(Const(id.name))
      case ListType(baseType) => Atom(InSynthTypeTransformer(leonType))
      case ArrayType(baseType) => Atom(InSynthTypeTransformer(leonType))
      case TupleType(baseTypes) => Atom(InSynthTypeTransformer(leonType))
      case SetType(baseType) => Atom(InSynthTypeTransformer(leonType))
      case MultisetType(baseType) => Atom(InSynthTypeTransformer(leonType))
      case MapType(from, to) => Atom(InSynthTypeTransformer(leonType))
      case FunctionType(froms, to) => transformFunction(to, froms)
      case c: ClassType => Atom(Const(c.id.name))
    }
  }

  private def transformFunction(fun: LeonType, params: List[LeonType]): DomainType = fun match {
    case FunctionType(froms, to) =>
      transformFunction(to, params ++ froms)
    case Untyped => throw new RuntimeException("Should not happen at this point")
    // query will have this
    case t =>
      Function( params map this, this(t) )
  }
  
}
