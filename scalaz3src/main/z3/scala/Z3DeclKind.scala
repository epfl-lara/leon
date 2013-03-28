package z3.scala

object Z3DeclKind extends Enumeration {
  type Z3DeclKind = Value

  val OpTrue = Value
  val OpFalse = Value
  val OpEq = Value
  val OpDistinct = Value
  val OpITE = Value
  val OpAnd = Value
  val OpOr = Value
  val OpIff = Value
  val OpXor = Value
  val OpNot = Value
  val OpImplies = Value
  val OpANum = Value
  val OpLE = Value
  val OpGE = Value
  val OpLT = Value
  val OpGT = Value
  val OpAdd = Value
  val OpSub = Value
  val OpUMinus = Value
  val OpMul = Value
  val OpDiv = Value
  val OpIDiv = Value
  val OpRem = Value
  val OpMod = Value
  val OpToReal = Value
  val OpToInt = Value
  val OpIsInt = Value
  val OpStore = Value
  val OpSelect = Value
  val OpConstArray = Value
  val OpArrayDefault = Value
  val OpArrayMap = Value
  val OpSetUnion = Value
  val OpSetIntersect = Value
  val OpSetDifference = Value
  val OpSetComplement = Value
  val OpSetSubset = Value
  val OpAsArray = Value

  val OpUninterpreted = Value

  val Other = Value
}
