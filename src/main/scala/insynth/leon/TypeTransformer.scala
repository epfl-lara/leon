package insynth.leon

import insynth.structures._

import leon.purescala.TypeTrees.{ TypeTree => LeonType, BottomType => LeonBottomType, _ }
import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions._

// enable postfix operations and implicit conversions
import scala.language.postfixOps
import scala.language.implicitConversions

object TypeTransformer extends ( LeonType => SuccinctType ) {
  
  def apply(typeDef: ClassTypeDef): SuccinctType = {    		
		implicit def singletonList(x: SuccinctType) = List(x)

    typeDef match {
      case abs: AbstractClassDef => Const(abs.id.name)
      case caseClassDef: CaseClassDef => Const(caseClassDef.id.name)
    }
  }
	
  def apply(leonType: LeonType): SuccinctType = {    		
		implicit def singletonList(x: SuccinctType) = List(x)

    leonType match {
      case Untyped => throw new RuntimeException("Should not happen at this point")
      case AnyType => Const("Any")
      case LeonBottomType => BottomType //Const("Bottom")
      case BooleanType => Const("Boolean")
      case UnitType => Const("Unit")
      case Int32Type => Const("Int")
      case ListType(baseType) => Instance("List", this(baseType) ) 
      case ArrayType(baseType) => Instance("Array", this(baseType) )
      case TupleType(baseTypes) => Instance("Tuple", baseTypes map { this(_) } toList )
      case SetType(baseType) => Instance("Set", this(baseType) )
      case MultisetType(baseType) => Instance("MultiSet", this(baseType) )
      case MapType(from, to) => Instance("Map", List( this(from), this(to) ))
      case FunctionType(froms, to) => transformFunction(to, froms)
      case c: ClassType => Const(c.id.name)
    }
  }

  private def transformFunction(fun: LeonType, params: List[LeonType]): SuccinctType = fun match {
    case FunctionType(froms, to) =>
      transformFunction(to, params ++ froms)
    case Untyped => throw new RuntimeException("Should not happen at this point")
    // query will have this
    case LeonBottomType =>
      Arrow( TSet(params map this distinct), this(fun) )
    case t =>
      Arrow( TSet(params map this distinct), this(t) )
  }
  
}