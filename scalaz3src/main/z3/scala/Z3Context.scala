package z3.scala

import dsl.Z3ASTWrapper
import z3.{Z3Wrapper,Pointer}
import scala.collection.mutable.{Set=>MutableSet}

object Z3Context {
  sealed abstract class ADTSortReference
  case class RecursiveType(index: Int) extends ADTSortReference
  case class RegularSort(sort: Z3Sort) extends ADTSortReference

  object AstPrintMode extends Enumeration {
    type AstPrintMode = Value
    val Z3_PRINT_SMTLIB_FULL, Z3_PRINT_LOW_LEVEL, Z3_PRINT_SMTLIB_COMPLIANT, Z3_PRINT_SMTLIB2_COMPLIANT = Value
  }
  import AstPrintMode._
}

sealed class Z3Context(val config: Z3Config) {
  val ptr : Long = Z3Wrapper.mkContextRC(config.ptr)

  val astQueue       = new Z3RefCountQueue[Z3ASTLike]()
  val astvectorQueue = new Z3RefCountQueue[Z3ASTVector]()
  val modelQueue     = new Z3RefCountQueue[Z3Model]()
  val solverQueue    = new Z3RefCountQueue[Z3Solver](5)
  val tacticQueue    = new Z3RefCountQueue[Z3Tactic]()

  def this(params : (String,Any)*) = this(new Z3Config(params : _*))

  private var deleted : Boolean = false
  override def finalize() : Unit = {
    if(!deleted) this.delete()
  }

  def delete() : Unit = {
    if(!deleted) {
      astQueue.clearQueue()
      modelQueue.clearQueue()
      solverQueue.clearQueue()
      astvectorQueue.clearQueue()
      tacticQueue.clearQueue()

      Z3Wrapper.delContext(this.ptr)
      deleted = true
    }
  }

  @deprecated("Use interrupt instead", "")
  def softCheckCancel() : Unit = {
    Z3Wrapper.interrupt(this.ptr)
  }

  override def toString : String = {
    Z3Wrapper.contextToString(this.ptr)
  }

  def astToString(ast: Z3AST) : String = {
    Z3Wrapper.astToString(this.ptr, ast.ptr)
  }

  def funcDeclToString(funcDecl: Z3FuncDecl) : String = {
    Z3Wrapper.funcDeclToString(this.ptr, funcDecl.ptr)
  }

  def sortToString(sort: Z3Sort) : String = {
    Z3Wrapper.sortToString(this.ptr, sort.ptr)
  }

  def patternToString(pattern: Z3Pattern) : String = {
    Z3Wrapper.patternToString(this.ptr, pattern.ptr)
  }

  def modelToString(model: Z3Model) : String = {
    Z3Wrapper.modelToString(this.ptr, model.ptr)
  }

  def benchmarkToSMTLIBString(name : String, logic : String, status : String, attributes : String, assumptions : Seq[Z3AST], formula : Z3AST) : String = {
    Z3Wrapper.benchmarkToSMTLIBString(this.ptr, name, logic, status, attributes, assumptions.size, toPtrArray(assumptions), formula.ptr)
  }

  def updateParamValue(paramID: String, paramValue: String) : Unit = {
    Z3Wrapper.updateParamValue(this.ptr, paramID, paramValue)
  }

  private val usedIntSymbols : MutableSet[Int] = MutableSet.empty
  private var lastUsed : Int = -1

  def mkIntSymbol(i: Int) : Z3Symbol = {
    usedIntSymbols += i
    new Z3Symbol(Z3Wrapper.mkIntSymbol(this.ptr, i), this)
  }

  def mkFreshIntSymbol : Z3Symbol = {
    var i = lastUsed + 1
    while(usedIntSymbols(i)) {
      i += 1
    }
    lastUsed = i
    mkIntSymbol(i)
  }

  private val usedStringSymbols : MutableSet[String] = MutableSet.empty
  def mkStringSymbol(s: String) : Z3Symbol = {
    usedStringSymbols += s
    new Z3Symbol(Z3Wrapper.mkStringSymbol(this.ptr, s), this)
  }

  def mkFreshStringSymbol(s: String) : Z3Symbol = {
    if(!usedStringSymbols(s)) {
      mkStringSymbol(s)
    } else {
      var i = 0
      while(usedStringSymbols(s + i)) {
        i += 1
      }
      mkStringSymbol(s + i)
    }
  }

  /*
  def isArrayValue(ast: Z3AST) : Option[Int] = {
    val numEntriesPtr = new Z3Wrapper.IntPtr()
    val result = Z3Wrapper.isArrayValue(this.ptr, ast.ptr, numEntriesPtr)
    if (result) {
      Some(numEntriesPtr.value)
    } else {
      None
    }
  }

  @deprecated("use `getArrayValue' in `Z3Model' instead")
  def getArrayValue(ast: Z3AST) : Option[(Map[Z3AST, Z3AST], Z3AST)] = isArrayValue(ast) match {
    case None => None
    case Some(numEntries) => {
      // val indices = (0 until numEntries).map(_ => new Z3AST((new Pointer(0L)).ptr, this)).toList
      // val values  = (0 until numEntries).map(_ => new Z3AST((new Pointer(0L)).ptr, this)).toList
      val indArray = new Array[Long](numEntries)
      val valArray = new Array[Long](numEntries)
      val elseValuePtr = new Pointer(0L)

      // println("indices before : " + indArray.toList.mkString(", "))
      // println("values  before : " + valArray.toList.mkString(", "))
      // println("else    before : " + elseValuePtr.ptr)

      Z3Wrapper.getArrayValue(this.ptr, ast.ptr, numEntries, indArray, valArray, elseValuePtr)

      // println("indices after : " + indArray.toList.mkString(", "))
      // println("values  after : " + valArray.toList.mkString(", "))
      // println("else    after : " + elseValuePtr.ptr)

      val elseValue = new Z3AST(elseValuePtr.ptr, this)
      val map = Map((indArray.map(new Z3AST(_, this)) zip valArray.map(new Z3AST(_, this))): _*)
      Some((map, elseValue))
    }
  }

  @deprecated("use `getSetValue' in `Z3Model' instead")
  def getSetValue(ast: Z3AST) : Option[Set[Z3AST]] = getArrayValue(ast) match {
    case None => None
    case Some((map, elseValue)) =>
      Some(map.filter(pair => getBoolValue(pair._2) == Some(true)).keySet.toSet)
  }
  */

  def isEqSort(s1: Z3Sort, s2: Z3Sort) : Boolean = {
    Z3Wrapper.isEqSort(this.ptr, s1.ptr, s2.ptr)
  }

  def mkUninterpretedSort(s: Z3Symbol) : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkUninterpretedSort(this.ptr, s.ptr), this)
  }

  def mkUninterpretedSort(s : String) : Z3Sort = {
    mkUninterpretedSort(mkStringSymbol(s))
  }

  def mkBoolSort() : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkBoolSort(this.ptr), this)
  }

  def mkIntSort() : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkIntSort(this.ptr), this)
  }

  def mkRealSort() : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkRealSort(this.ptr), this)
  }
  
  import Z3Context.{ADTSortReference,RecursiveType,RegularSort}

  def mkADTSorts(defs: Seq[(String, Seq[String], Seq[Seq[(String,ADTSortReference)]])]) : Seq[(Z3Sort, Seq[Z3FuncDecl], Seq[Z3FuncDecl], Seq[Seq[Z3FuncDecl]])] = {
    val typeCount: Int = defs.size

    // the following big block builds the following three lists
    var symbolList:   List[Z3Symbol] = Nil
    var consListList: List[Long] = Nil
    var consScalaList: List[List[(Long,Int)]] = Nil // in the Scala list, we maintain number of fields

    for(tuple <- defs) yield {
      val (typeName, typeConstructorNames, typeConstructorArgs) = tuple
      val constructorCount: Int = typeConstructorNames.size
      if(constructorCount != typeConstructorArgs.size) {
        throw new IllegalArgumentException("sequence of constructor names should have the same size as sequence of constructor param lists, for type " + typeName)
      }

      val sym: Z3Symbol = mkStringSymbol(typeName)
      symbolList = sym :: symbolList

      val constructors = (for((tcn, tca) <- (typeConstructorNames zip typeConstructorArgs)) yield {
        val consSym: Z3Symbol = mkStringSymbol(tcn)
        val testSym: Z3Symbol = mkStringSymbol("is" + tcn)
        val fieldSyms: Array[Long] = tca.map(p => mkStringSymbol(p._1).ptr).toArray
        val fieldSorts: Array[Long] = tca.map(p => p._2 match {
          case RecursiveType(idx) if idx >= typeCount => throw new IllegalArgumentException("index of recursive type is too big (" + idx + ") for field " + p._1 + " of type " + typeName)
          case RegularSort(srt) => srt.ptr
          case RecursiveType(_) => 0L
        }).toArray

        val fieldRefs: Array[Int] = tca.map(p => p._2 match {
          case RegularSort(_) => 0
          case RecursiveType(idx) => idx
        }).toArray

        val consPtr = Z3Wrapper.mkConstructor(this.ptr, consSym.ptr, testSym.ptr, fieldSyms.size, fieldSyms, fieldSorts, fieldRefs)
        (consPtr, fieldSyms.size)
      })

      val consArr = constructors.map(_._1).toArray
      val consList = Z3Wrapper.mkConstructorList(this.ptr, consArr.length, consArr)
      consListList = consList :: consListList
      consScalaList = constructors.toList :: consScalaList
    }

    symbolList   = symbolList.reverse
    consListList = consListList.reverse
    consScalaList = consScalaList.reverse
    
    val newSorts: Array[Long] = Z3Wrapper.mkDatatypes(this.ptr, typeCount, toPtrArray(symbolList), consListList.toArray)

    consListList.foreach(cl => Z3Wrapper.delConstructorList(this.ptr, cl))
    
    for((sort, consLst) <- (newSorts zip consScalaList)) yield {
      val zipped = for (cons <- consLst) yield {
        val consFunPtr = new Pointer(0L)
        val testFunPtr = new Pointer(0L)

        val selectors: Array[Long] = if(cons._2 > 0) new Array[Long](cons._2) else null

        Z3Wrapper.queryConstructor(this.ptr, cons._1, cons._2, consFunPtr, testFunPtr, selectors)

        val consFun = new Z3FuncDecl(consFunPtr.ptr, cons._2, this)
        val testFun = new Z3FuncDecl(testFunPtr.ptr, 1, this)
        (consFun, (testFun, if(cons._2 > 0) selectors.map(new Z3FuncDecl(_, 1, this)).toList else Nil))
      }

      val (consFuns, unzippedOnce) = zipped.unzip
      val (testFuns, selectorFunss) = unzippedOnce.unzip
  
      (new Z3Sort(sort, this), consFuns, testFuns, selectorFunss)
    }
  }

  def isEqAST(t1: Z3AST, t2: Z3AST) : Boolean = {
    Z3Wrapper.isEqAST(this.ptr, t1.ptr, t2.ptr)
  }

  def mkApp(funcDecl: Z3FuncDecl, args: Z3AST*) : Z3AST = {
    if(funcDecl.arity != args.size)
      throw new IllegalArgumentException("Calling mkApp with wrong number of arguments.")

    new Z3AST(Z3Wrapper.mkApp(this.ptr, funcDecl.ptr, args.size, toPtrArray(args)), this)
  }

  def isEqFuncDecl(fd1: Z3FuncDecl, fd2: Z3FuncDecl) : Boolean = {
    Z3Wrapper.isEqFuncDecl(this.ptr, fd1.ptr, fd2.ptr)
  }

  def mkConst(symbol: Z3Symbol, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.mkConst(this.ptr, symbol.ptr, sort.ptr), this)
  }

  def mkConst(s: String, sort: Z3Sort) : Z3AST = {
    mkConst(mkStringSymbol(s), sort)
  }

  def mkIntConst(symbol: Z3Symbol) : Z3AST = {
    mkConst(symbol, mkIntSort)
  }

  def mkIntConst(s: String) : Z3AST = {
    mkIntConst(mkStringSymbol(s))
  }

  def mkBoolConst(symbol: Z3Symbol) : Z3AST = {
    mkConst(symbol, mkBoolSort)
  }

  def mkBoolConst(s: String) : Z3AST = {
    mkBoolConst(mkStringSymbol(s))
  }

  def mkFuncDecl(symbol: Z3Symbol, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = {
    new Z3FuncDecl(Z3Wrapper.mkFuncDecl(this.ptr, symbol.ptr, domainSorts.size, toPtrArray(domainSorts), rangeSort.ptr), domainSorts.size, this)
  }

  def mkFuncDecl(symbol: Z3Symbol, domainSort: Z3Sort, rangeSort: Z3Sort) : Z3FuncDecl = {
    mkFuncDecl(symbol, Seq(domainSort), rangeSort)
  }

  def mkFuncDecl(symbol: String, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = {
    mkFuncDecl(mkStringSymbol(symbol), domainSorts, rangeSort)
  }

  def mkFuncDecl(symbol: String, domainSort: Z3Sort, rangeSort: Z3Sort) : Z3FuncDecl = {
    mkFuncDecl(mkStringSymbol(symbol), Seq(domainSort), rangeSort)
  }

  def mkFreshConst(prefix: String, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.mkFreshConst(this.ptr, prefix, sort.ptr), this)
  }

  def mkFreshIntConst(prefix: String) : Z3AST = {
    mkFreshConst(prefix, mkIntSort)
  }

  def mkFreshBoolConst(prefix: String) : Z3AST = {
    mkFreshConst(prefix, mkBoolSort)
  }

  def mkFreshFuncDecl(prefix: String, domainSorts: Seq[Z3Sort], rangeSort: Z3Sort) : Z3FuncDecl = {
    new Z3FuncDecl(Z3Wrapper.mkFreshFuncDecl(this.ptr, prefix, domainSorts.size, toPtrArray(domainSorts), rangeSort.ptr), domainSorts.size, this)
  }

  def mkTrue() : Z3AST = {
    new Z3AST(Z3Wrapper.mkTrue(this.ptr), this)
  }

  def mkFalse() : Z3AST = {
    new Z3AST(Z3Wrapper.mkFalse(this.ptr), this)
  }

  def mkEq(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkEq(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkDistinct(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkDistinct needs at least one argument")
    } else if(args.size == 1) {
      mkTrue
    } else {
      new Z3AST(Z3Wrapper.mkDistinct(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkNot(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkNot(this.ptr, ast.ptr), this)
  }

  def mkITE(t1: Z3AST, t2: Z3AST, t3: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkITE(this.ptr, t1.ptr, t2.ptr, t3.ptr), this)
  }

  def mkIff(t1: Z3AST, t2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkIff(this.ptr, t1.ptr, t2.ptr), this)
  }

  def mkImplies(t1: Z3AST, t2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkImplies(this.ptr, t1.ptr, t2.ptr), this)
  }

  def mkXor(t1: Z3AST, t2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkXor(this.ptr, t1.ptr, t2.ptr), this)
  }

  def mkAnd(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkAnd needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkAnd(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkOr(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkOr needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkOr(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkAdd(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkAdd needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkAdd(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkMul(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkMul needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkMul(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkSub(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkSub needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkSub(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkUnaryMinus(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkUnaryMinus(this.ptr, ast.ptr), this)
  }

  def mkDiv(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkDiv(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkMod(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkMod(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkRem(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkRem(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkLT(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkLT(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkLE(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkLE(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkGT(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkGT(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkGE(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkGE(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkInt2Real(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkInt2Real(this.ptr, ast.ptr), this)
  }

  def mkReal2Int(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkReal2Int(this.ptr, ast.ptr), this)
  }

  def mkIsInt(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkIsInt(this.ptr, ast.ptr), this)
  }

  def mkArraySort(domain: Z3Sort, range: Z3Sort) : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkArraySort(this.ptr, domain.ptr, range.ptr), this)
  }

  def mkSelect(array: Z3AST, index: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSelect(this.ptr, array.ptr, index.ptr), this)
  }

  def mkStore(array: Z3AST, index: Z3AST, value: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkStore(this.ptr, array.ptr, index.ptr, value.ptr), this)
  }

  def mkConstArray(sort: Z3Sort, value: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkConstArray(this.ptr, sort.ptr, value.ptr), this)
  }

  def mkArrayDefault(array: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkArrayDefault(this.ptr, array.ptr), this)
  }

  def mkTupleSort(name : Z3Symbol, sorts : Z3Sort*) : (Z3Sort,Z3FuncDecl,Seq[Z3FuncDecl]) = {
    require(sorts.size > 0)
    val sz = sorts.size
    val consPtr = new Pointer(0L)
    val projFuns = new Array[Long](sz)
    val fieldNames = sorts.map(s => mkFreshStringSymbol(name + "-field")).toArray
    val sortPtr = Z3Wrapper.mkTupleSort(this.ptr, name.ptr, sz, fieldNames.map(_.ptr), sorts.map(_.ptr).toArray, consPtr, projFuns)
    val newSort = new Z3Sort(sortPtr, this)
    val consFuncDecl = new Z3FuncDecl(consPtr.ptr, sz, this)
    val projFuncDecls = projFuns.map(ptr => new Z3FuncDecl(ptr, 1, this)).toSeq
    (newSort, consFuncDecl, projFuncDecls)
  }

  def mkTupleSort(name : String, sorts : Z3Sort*) : (Z3Sort,Z3FuncDecl,Seq[Z3FuncDecl]) = mkTupleSort(mkStringSymbol(name), sorts : _*)

  def mkSetSort(underlying: Z3Sort) : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkSetSort(this.ptr, underlying.ptr), this)
  }

  def mkEmptySet(sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.mkEmptySet(this.ptr, sort.ptr), this)
  }

  def mkFullSet(sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.mkFullSet(this.ptr, sort.ptr), this)
  }

  def mkSetAdd(set: Z3AST, elem: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSetAdd(this.ptr, set.ptr, elem.ptr), this)
  }

  def mkSetDel(set: Z3AST, elem: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSetDel(this.ptr, set.ptr, elem.ptr), this)
  }

  def mkSetUnion(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkSetUnion needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkSetUnion(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkSetIntersect(args: Z3AST*) : Z3AST = {
    if(args.size == 0) {
      throw new IllegalArgumentException("mkSetIntersect needs at least one argument")
    } else if(args.size == 1) {
      new Z3AST(args(0).ptr, this)
    } else {
      new Z3AST(Z3Wrapper.mkSetIntersect(this.ptr, args.length, toPtrArray(args)), this)
    }
  }

  def mkSetDifference(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSetDifference(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkSetComplement(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSetComplement(this.ptr, ast.ptr), this)
  }

  def mkSetMember(elem: Z3AST, set: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSetMember(this.ptr, elem.ptr, set.ptr), this)
  }

  def mkSetSubset(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSetSubset(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkInt(value: Int, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.mkInt(this.ptr, value, sort.ptr), this)
  }
  
  def mkReal(numerator: Int, denominator: Int) : Z3AST = {
    new Z3AST(Z3Wrapper.mkReal(this.ptr, numerator, denominator), this)
  }

  def mkPattern(args: Z3AST*) : Z3Pattern = {
    new Z3Pattern(Z3Wrapper.mkPattern(this.ptr, args.size, toPtrArray(args)), this)
  }

  def mkBound(index: Int, sort: Z3Sort) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBound(this.ptr, index, sort.ptr), this)
  }

  def mkForAll(weight: Int, patterns: Seq[Z3Pattern], decls: Seq[(Z3Symbol,Z3Sort)], body: Z3AST) : Z3AST = mkQuantifier(true, weight, patterns, decls, body)

  def mkExists(weight: Int, patterns: Seq[Z3Pattern], decls: Seq[(Z3Symbol,Z3Sort)], body: Z3AST) : Z3AST = mkQuantifier(false, weight, patterns, decls, body)

  def mkQuantifier(isForAll: Boolean, weight: Int, patterns: Seq[Z3Pattern], decls: Seq[(Z3Symbol,Z3Sort)], body: Z3AST) : Z3AST = {
    val (declSyms, declSorts) = decls.unzip
    new Z3AST(
      Z3Wrapper.mkQuantifier(
        this.ptr,
        isForAll,
        weight,
        patterns.size,
        toPtrArray(patterns),
        decls.size,
        toPtrArray(declSorts),
        toPtrArray(declSyms),
        body.ptr),
      this
    )
  }

  def mkBVSort(size: Int) : Z3Sort = {
    new Z3Sort(Z3Wrapper.mkBVSort(this.ptr, size), this)
  }

  def mkBVNot(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVNot(this.ptr, ast.ptr), this)
  }

  def mkBVRedAnd(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVRedAnd(this.ptr, ast.ptr), this)
  }

  def mkBVRedOr(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVRedOr(this.ptr, ast.ptr), this)
  }

  def mkBVAnd(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVAnd(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVOr(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVOr(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVXor(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVXor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVNand(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVNand(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVNor(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVNor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVXnor(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVXnor(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVNeg(ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVNeg(this.ptr, ast.ptr), this)
  }

  def mkBVAdd(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVAdd(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSub(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSub(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVMul(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVMul(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUdiv(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVUdiv(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSdiv(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSdiv(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUrem(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVUrem(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSrem(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSrem(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSmod(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSmod(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUlt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVUlt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSlt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSlt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUle(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVUle(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSle(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSle(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUgt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVUgt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSgt(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSgt(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVUge(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVUge(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVSge(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVSge(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkConcat(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkConcat(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkExtract(high: Int, low: Int, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkExtract(this.ptr, high, low, ast.ptr), this)
  }

  def mkSignExt(extraSize: Int, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkSignExt(this.ptr, extraSize, ast.ptr), this)
  }

  def mkZeroExt(extraSize: Int, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkZeroExt(this.ptr, extraSize, ast.ptr), this)
  }

  def mkBVShl(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVShl(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVLshr(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVLshr(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVAshr(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVAshr(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkExtRotateLeft(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkExtRotateLeft(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkExtRotateRight(ast1: Z3AST, ast2: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkExtRotateRight(this.ptr, ast1.ptr, ast2.ptr), this)
  }

  def mkBVAddNoOverflow(ast1: Z3AST, ast2: Z3AST, isSigned: Boolean) : Z3AST = {
    new Z3AST(Z3Wrapper.mkBVAddNoOverflow(this.ptr, ast1.ptr, ast2.ptr, isSigned), this)
  }

  def getSymbolKind(symbol: Z3Symbol) : Z3SymbolKind[_] = {
    Z3Wrapper.getSymbolKind(this.ptr, symbol.ptr) match {
      case 0 => Z3IntSymbol(getSymbolInt(symbol))
      case 1 => Z3StringSymbol(getSymbolString(symbol))
      case other => error("Z3_get_symbol_kind returned an unknown value : " + other)
    }
  }

  private[z3] def getSymbolInt(symbol: Z3Symbol) : Int = {
    Z3Wrapper.getSymbolInt(this.ptr, symbol.ptr)
  }

  private[z3] def getSymbolString(symbol: Z3Symbol) : String = {
    Z3Wrapper.getSymbolString(this.ptr, symbol.ptr)
  }

  def getASTKind(ast: Z3AST) : Z3ASTKind = {
    Z3Wrapper.getASTKind(this.ptr, ast.ptr) match {
      case 0 => Z3NumeralAST(getNumeralInt(ast))
      case 1 => {
        val numArgs = getAppNumArgs(ast)
        val args = (Seq.tabulate(numArgs)){ i => getAppArg(ast, i) }
        Z3AppAST(getAppDecl(ast, numArgs), args)
      }
      case 2 => {
        val index = getIndexValue(ast)
        Z3VarAST(index)
      }
      case 3 => {
        val body = getQuantifierBody(ast)
        val forall = isQuantifierForall(ast)
        val numVars = getQuantifierNumBound(ast)
        val varSymbols = (0 to numVars-1).map(getQuantifierBoundName(ast, _))
        val varNames = varSymbols.map(x => getSymbolKind(x) match { case Z3IntSymbol(x) => "#" + x.toString(); case Z3StringSymbol(s) => s})
        Z3QuantifierAST(forall, varNames, body)
      }
      case _ => Z3UnknownAST
    }
  }

  def getIndexValue(ast: Z3AST) : Int = {
    return Z3Wrapper.getIndexValue(this.ptr, ast.ptr)
  }

  def isQuantifierForall(ast: Z3AST) : Boolean = {
    return Z3Wrapper.isQuantifierForall(this.ptr, ast.ptr)
  }

  def getQuantifierBody(ast: Z3AST) : Z3AST = {
    return new Z3AST(Z3Wrapper.getQuantifierBody(this.ptr, ast.ptr), this)
  }

  def getQuantifierBoundName(ast: Z3AST, i: Int) : Z3Symbol = {
    return new Z3Symbol(Z3Wrapper.getQuantifierBoundName(this.ptr, ast.ptr, i), this)
  }

  def getQuantifierNumBound(ast: Z3AST) : Int = {
    return Z3Wrapper.getQuantifierNumBound(this.ptr, ast.ptr)
  }

  def getDeclKind(funcDecl: Z3FuncDecl) : Z3DeclKind.Value = {
    import Z3DeclKind._

    Z3Wrapper.getDeclKind(this.ptr, funcDecl.ptr) match {
      case  0 => OpTrue 
      case  1 => OpFalse 
      case  2 => OpEq 
      case  3 => OpDistinct 
      case  4 => OpITE 
      case  5 => OpAnd 
      case  6 => OpOr 
      case  7 => OpIff 
      case  8 => OpXor 
      case  9 => OpNot 
      case 10 => OpImplies 
      case 11 => OpANum 
      case 12 => OpLE 
      case 13 => OpGE 
      case 14 => OpLT 
      case 15 => OpGT 
      case 16 => OpAdd 
      case 17 => OpSub 
      case 18 => OpUMinus 
      case 19 => OpMul 
      case 20 => OpDiv 
      case 21 => OpIDiv 
      case 22 => OpRem 
      case 23 => OpMod 
      case 24 => OpToReal 
      case 25 => OpToInt 
      case 26 => OpIsInt 
      case 27 => OpStore 
      case 28 => OpSelect 
      case 29 => OpConstArray 
      case 30 => OpArrayDefault 
      case 31 => OpArrayMap 
      case 32 => OpSetUnion 
      case 33 => OpSetIntersect 
      case 34 => OpSetDifference 
      case 35 => OpSetComplement 
      case 36 => OpSetSubset 
      case 37 => OpAsArray 
      case 1000 => OpUninterpreted
      case 9999 => Other 
      case other => error("Unhandled int code for Z3KindDecl: " + other)
    }
  }

  def getAppDecl(ast: Z3AST, arity: Int = -1) : Z3FuncDecl = {
    val ad = Z3Wrapper.getAppDecl(this.ptr, ast.ptr)
    val ary = if(arity > -1) arity else Z3Wrapper.getDomainSize(this.ptr, ad)
    new Z3FuncDecl(ad, ary, this)
  }

  private def getAppNumArgs(ast: Z3AST) : Int = {
    Z3Wrapper.getAppNumArgs(this.ptr, ast.ptr)
  }

  private def getAppArg(ast: Z3AST, i: Int) : Z3AST = {
    new Z3AST(Z3Wrapper.getAppArg(this.ptr, ast.ptr, i), this)
  }

  def getDeclName(fd: Z3FuncDecl) : Z3Symbol = {
    new Z3Symbol(Z3Wrapper.getDeclName(this.ptr, fd.ptr), this)
  }

  // TODO arity
  def getDeclFuncDeclParameter(fd: Z3FuncDecl, idx: Int, arity: Int = 1) : Z3FuncDecl = {
    new Z3FuncDecl(Z3Wrapper.getDeclFuncDeclParameter(this.ptr, fd.ptr, idx), arity, this)
  }

  def getSort(ast: Z3AST) : Z3Sort = {
    new Z3Sort(Z3Wrapper.getSort(this.ptr, ast.ptr), this)
  }

  def getDomainSize(funcDecl: Z3FuncDecl) : Int = funcDecl.arity

  def getDomain(funcDecl: Z3FuncDecl, i: Int) : Z3Sort = {
    if(funcDecl.arity <= i)
      throw new IllegalArgumentException("Calling getDomain with too large index.")

    new Z3Sort(Z3Wrapper.getDomain(this.ptr, funcDecl.ptr, i), this)
  }

  def getRange(funcDecl: Z3FuncDecl) : Z3Sort = {
    new Z3Sort(Z3Wrapper.getRange(this.ptr, funcDecl.ptr), this)
  }

  def getNumeralInt(ast: Z3AST) : Option[Int] = {
    val ip = new Z3Wrapper.IntPtr
    val res = Z3Wrapper.getNumeralInt(this.ptr, ast.ptr, ip)
    if(res)
      Some(ip.value)
    else
      None
  }

  def getBoolValue(ast: Z3AST) : Option[Boolean] = {
    val res = i2ob(Z3Wrapper.getBoolValue(this.ptr, ast.ptr))
    res
  }

  // This is deprecated, we don't want to go directly through Contexts for
  // this, but via Solver

  private lazy val globalSolver = mkSolver()

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def push() : Unit = {
    globalSolver.push()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def pop(numScopes : Int = 1) : Unit = {
    globalSolver.pop(numScopes)
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def getNumScopes() : Int = {
    globalSolver.getNumScopes()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def assertCnstr(ast: Z3AST) : Unit = {
    globalSolver.assertCnstr(ast)
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def assertCnstr(tree : dsl.Tree[dsl.BoolSort]) : Unit = {
    globalSolver.assertCnstr(tree.ast(this))
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def check() : Option[Boolean] = {
    globalSolver.check()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAndGetModel() : (Option[Boolean],Z3Model) = {
    globalSolver.checkAndGetModel()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAssumptions(assumptions: Z3AST*) : (Option[Boolean],Z3Model,Seq[Z3AST]) = {
    val res   = globalSolver.checkAssumptions(assumptions : _*)
    val model = if (res != Some(false)) globalSolver.getModel() else null
    val core  = if (res != Some(true)) globalSolver.getUnsatCore().toSeq else Seq()

    (res, model, core)
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAndGetAllModels(): Iterator[Z3Model] = {
    globalSolver.checkAndGetAllModels()
  }

  @deprecated("You should go through Z3Solver via mkSolver first", "")
  def checkAndGetAllEventualModels(): Iterator[(Option[Boolean], Z3Model)] = {
    globalSolver.checkAndGetAllEventualModels()
  }

  @deprecated("You should use Z3Solver.getReasonUnknown", "")
  def getSearchFailure : Z3SearchFailure = {
    Z3Wrapper.getSearchFailure(this.ptr) match {
      case 0 => Z3NoFailure
      case 1 => Z3Unknown
      case 2 => Z3Timeout
      case 3 => Z3MemoutWatermark
      case 4 => Z3Canceled
      case 5 => Z3NumConflicts
      case 6 => Z3IncompleteTheory
      case 7 => Z3Quantifiers
      case _ => Z3Timeout
    }
  }

  def mkLabel(symbol: Z3Symbol, polarity: Boolean, ast: Z3AST) : Z3AST = {
    new Z3AST(Z3Wrapper.mkLabel(this.ptr, symbol.ptr, polarity, ast.ptr), this)
  }

//  def getRelevantLabels : Z3Literals = {
//    new Z3Literals(Z3Wrapper.getRelevantLabels(this.ptr), this)
//  }

  def getRelevantLiterals : Z3Literals = {
    new Z3Literals(Z3Wrapper.getRelevantLiterals(this.ptr), this)
  }

  def getGuessedLiterals : Z3Literals = {
    new Z3Literals(Z3Wrapper.getGuessedLiterals(this.ptr), this)
  }

// in Z3Literals instead
//  def delLiterals(lbls: Z3Literals) : Unit = {
//    Z3Wrapper.delLiterals(this.ptr, lbls.ptr)
//  }

  def getNumLiterals(lbls: Z3Literals) : Int = {
    Z3Wrapper.getNumLiterals(this.ptr, lbls.ptr)
  }

//  def getLabelSymbol(lbls: Z3Literals, idx: Int) : Z3Symbol = {
//    new Z3Symbol(Z3Wrapper.getLabelSymbol(this.ptr, lbls.ptr, idx), this)
//  }

  def getLiteral(lbls: Z3Literals, idx: Int) : Z3AST = {
    new Z3AST(Z3Wrapper.getLiteral(this.ptr, lbls.ptr, idx), this)
  }

  def disableLiteral(lbls: Z3Literals, idx: Int) : Unit = {
    Z3Wrapper.disableLiteral(this.ptr, lbls.ptr, idx)
  }

  def blockLiterals(lbls: Z3Literals) : Unit = {
    Z3Wrapper.blockLiterals(this.ptr, lbls.ptr)
  }

  // Parser interface
  private def parseSMTLIB(file: Boolean, str: String) : Unit = {
    if(file) {
      Z3Wrapper.parseSMTLIBFile(this.ptr, str, 0, null, null, 0, null, null)
    } else {
      Z3Wrapper.parseSMTLIBString(this.ptr, str, 0, null, null, 0, null, null)
    }
  }
  private def parseSMTLIB2(file: Boolean, str: String) : Z3AST = {
    if(file) {
      new Z3AST(Z3Wrapper.parseSMTLIB2File(this.ptr, str, 0, null, null, 0, null, null), this)
    } else {
      new Z3AST(Z3Wrapper.parseSMTLIB2String(this.ptr, str, 0, null, null, 0, null, null), this)
    }
  }
  private def parseSMTLIB(file: Boolean, str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Unit = {
    val (sortNames, z3Sorts) = sorts.unzip
    val (declNames, z3Decls) = decls.unzip
    if(file) {
      Z3Wrapper.parseSMTLIBFile(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls))
    } else {
      Z3Wrapper.parseSMTLIBString(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls))
    }
  }
  private def parseSMTLIB2(file: Boolean, str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Z3AST = {
    val (sortNames, z3Sorts) = sorts.unzip
    val (declNames, z3Decls) = decls.unzip
    if(file) {
      new Z3AST(Z3Wrapper.parseSMTLIB2File(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls)), this)
    } else {
      new Z3AST(Z3Wrapper.parseSMTLIB2String(this.ptr, str, sorts.size, toPtrArray(sortNames), toPtrArray(z3Sorts), decls.size, toPtrArray(declNames), toPtrArray(z3Decls)), this)
    }
  }

  /** Uses the SMT-LIB parser to read in a benchmark file.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBFile(fileName: String) : Unit = parseSMTLIB(true, fileName)

  /** Uses the SMT-LIB parser to read in a benchmark string.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBString(str: String) : Unit = parseSMTLIB(false, str)

  /** Uses the SMT-LIB parser to read in a benchmark file. The maps are used to override symbols that would otherwise be created by the parser.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBFile(fileName: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Unit = parseSMTLIB(true, fileName, sorts, decls)

  /** Uses the SMT-LIB parser to read in a benchmark string. The maps are used to override symbols that would otherwise be created by the parser.
   *  @see getSMTLIBFormulas, getSMTLIBAssumptions, getSMTLIBDecls, getSMTLIBSorts, getSMTLIBError
   */
  def parseSMTLIBString(str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Unit = parseSMTLIB(false, str, sorts, decls)

  /** Uses the SMT-LIB 2 parser to read in a benchmark file.
   */
  def parseSMTLIB2File(fileName: String) : Z3AST = parseSMTLIB2(true, fileName)

  /** Uses the SMT-LIB 2 parser to read in a benchmark string.
   */
  def parseSMTLIB2String(str: String) : Z3AST = parseSMTLIB2(false, str)

  /** Uses the SMT-LIB 2 parser to read in a benchmark file. The maps are used to override symbols that would otherwise be created by the parser.
   */
  def parseSMTLIB2File(fileName: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Z3AST = parseSMTLIB2(true, fileName, sorts, decls)

  /** Uses the SMT-LIB 2 parser to read in a benchmark string. The maps are used to override symbols that would otherwise be created by the parser.
   */
  def parseSMTLIB2String(str: String, sorts: Map[Z3Symbol,Z3Sort], decls: Map[Z3Symbol,Z3FuncDecl]) : Z3AST = parseSMTLIB2(false, str, sorts, decls)

  /** Returns an iterator of the formulas created by the SMT-LIB parser. */
  def getSMTLIBFormulas : Iterator[Z3AST] = {
    val ctx = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.getSMTLIBNumFormulas(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.getSMTLIBFormula(ctx.ptr, returned), ctx)
        returned += 1
        toReturn
      }
    }
  }

  /** Returns an iterator of the assumptions created by the SMT-LIB parser. */
  def getSMTLIBAssumptions : Iterator[Z3AST] = {
    val ctx = this
    new Iterator[Z3AST] {
      val total : Int = Z3Wrapper.getSMTLIBNumAssumptions(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3AST = {
        val toReturn = new Z3AST(Z3Wrapper.getSMTLIBAssumption(ctx.ptr, returned), ctx)
        returned += 1
        toReturn
      }
    }
  }

  /** Returns an iterator of the function and constant declarations created by the SMT-LIB parser. */
  def getSMTLIBDecls : Iterator[Z3FuncDecl] = {
    val ctx = this
    new Iterator[Z3FuncDecl] {
      val total : Int = Z3Wrapper.getSMTLIBNumDecls(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3FuncDecl = {
        val fdPtr = Z3Wrapper.getSMTLIBDecl(ctx.ptr, returned)
        val arity = Z3Wrapper.getDomainSize(ctx.ptr, fdPtr)
        val toReturn = new Z3FuncDecl(Z3Wrapper.getSMTLIBDecl(ctx.ptr, returned), arity, ctx)
        returned += 1
        toReturn
      }
    }
  }

  /** Returns an iterator of the sorts created by the SMT-LIB parser. */
  def getSMTLIBSorts : Iterator[Z3Sort] = {
    val ctx = this
    new Iterator[Z3Sort] {
      val total : Int = Z3Wrapper.getSMTLIBNumSorts(ctx.ptr)
      var returned : Int = 0

      override def hasNext : Boolean = (returned < total)
      override def next() : Z3Sort = {
        val toReturn = new Z3Sort(Z3Wrapper.getSMTLIBSort(ctx.ptr, returned), ctx)
        returned += 1
        toReturn
      }
    }
  }

  def substitute(ast : Z3AST, from : Array[Z3AST], to : Array[Z3AST]) : Z3AST = {
    if (from.length != to.length)
      throw new IllegalArgumentException("from and to must have the same length");
    return new Z3AST(Z3Wrapper.substitute(this.ptr, ast.ptr, from.length, from.map(_.ptr), to.map(_.ptr)), this);
  }

  def setAstPrintMode(printMode : Z3Context.AstPrintMode.AstPrintMode) = {
    var mode : Int = 0
    printMode match {
      case Z3Context.AstPrintMode.Z3_PRINT_SMTLIB_FULL => mode = 0
      case Z3Context.AstPrintMode.Z3_PRINT_LOW_LEVEL => mode = 1
      case Z3Context.AstPrintMode.Z3_PRINT_SMTLIB_COMPLIANT => mode = 2
      case Z3Context.AstPrintMode.Z3_PRINT_SMTLIB2_COMPLIANT => mode = 3
    }
    Z3Wrapper.setAstPrintMode(this.ptr, mode);
  }

  def simplifyAst(ast : Z3AST) : Z3AST = {
    return new Z3AST(Z3Wrapper.simplify(this.ptr, ast.ptr), this);
  }

  def mkForAllConst(weight: Int, patterns: Seq[Z3Pattern], bounds: Seq[Z3AST], body: Z3AST) : Z3AST = mkQuantifierConst(true, weight, patterns, bounds, body)

  def mkExistsConst(weight: Int, patterns: Seq[Z3Pattern], bounds: Seq[Z3AST], body: Z3AST) : Z3AST = mkQuantifierConst(false, weight, patterns, bounds, body)

  def mkQuantifierConst(isForAll: Boolean, weight: Int, patterns: Seq[Z3Pattern], bounds: Seq[Z3AST], body: Z3AST) : Z3AST = {
    new Z3AST(
      Z3Wrapper.mkQuantifierConst(
        this.ptr,
        isForAll,
        weight,
        bounds.size,
        toPtrArray(bounds),
        patterns.size,
        toPtrArray(patterns),
        body.ptr),
      this
    )
  }

  def mkTactic(name: String) : Z3Tactic = {
    return new Z3Tactic(Z3Wrapper.mkTactic(this.ptr, name), this)
  }

  def mkTacticAndThen(tactic1: Z3Tactic, tactic2: Z3Tactic) : Z3Tactic = {
    return new Z3Tactic(Z3Wrapper.tacticAndThen(this.ptr, tactic1.ptr, tactic2.ptr), this)
  }

  def mkSolver() : Z3Solver = {
    new Z3Solver(Z3Wrapper.mkSolver(this.ptr), this)
  }

  def mkSolverFromTactic(tactic: Z3Tactic) : Z3Solver = {
    new Z3Solver(Z3Wrapper.mkSolverFromTactic(this.ptr, tactic.ptr), this)
  }

  def interrupt() = {
    Z3Wrapper.interrupt(this.ptr)
  }

  /** Returns the last error issued by the SMT-LIB parser. */
  def getSMTLIBError : String = Z3Wrapper.getSMTLIBError(this.ptr)
}
