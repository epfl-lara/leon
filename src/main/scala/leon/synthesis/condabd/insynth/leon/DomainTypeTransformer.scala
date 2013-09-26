package leon.synthesis.condabd.insynth.leon

import insynth.structures._

import leon.purescala.TypeTrees.{ TypeTree => LeonType, BottomType => LeonBottomType, _ }
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions._

import scala.language.implicitConversions

object DomainTypeTransformer extends ( LeonType => DomainType ) {
  
  val InSynthTypeTransformer = TypeTransformer
  
  def apply(typeDef: ClassTypeDef): DomainType = {    		
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
      case AnyType => Atom(Const("Any"))
      case LeonBottomType => Atom(BottomType) //Atom(Const("Bottom"))
      case BooleanType => Atom(Const("Boolean"))
      case UnitType => Atom(Const("Unit"))
      case Int32Type => Atom(Const("Int"))
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
    case LeonBottomType =>
      Function( params map this, this(fun) )
    case t =>
      Function( params map this, this(t) )
  }
  
}