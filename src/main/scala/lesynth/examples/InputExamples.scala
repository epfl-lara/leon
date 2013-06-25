package lesynth
package examples

import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.TreeOps
import leon.purescala.Common.Identifier
import leon.evaluators.Evaluator
import leon.synthesis.Problem
import leon.purescala.DataGen

import insynth.leon.loader.{ HoleExtractor, LeonLoader }

object InputExamples {
  import DataGen._
  
  val rnd = new scala.util.Random(System.currentTimeMillis)
  val MAX_INT = 1000

  def getDataGenInputExamples(evaluator: Evaluator, p: Problem,
    numOfModels: Int, numOfTries: Int, _forcedFreeVars: Option[Seq[Identifier]]) = {
    val models = findModels(p.pc, evaluator, numOfModels, numOfTries,
      forcedFreeVars = _forcedFreeVars)

    models.toList
  }
  
  def getDataGenInputExamplesRandomIntegers(evaluator: Evaluator, p: Problem,
    numOfModels: Int, numOfTries: Int, _forcedFreeVars: Option[Seq[Identifier]],
    bound: Int = MAX_INT) = {
    import TreeOps._
    
    val models = findModels(p.pc, evaluator, numOfModels, numOfTries,
      forcedFreeVars = _forcedFreeVars)

    def foundInteger(x: Expr) = x match {
      case _:IntLiteral => Some(IntLiteral(rnd.nextInt(bound)))
      case _ => None
    }
      
    models.toList.map( innerMap =>
      innerMap.map( innerEl => innerEl match {
        case (id, expr) => (id, searchAndReplace(foundInteger)(expr))
      })
    )
  }

  def getFixedInputExamples(argumentIds: Seq[Identifier], loader: LeonLoader) = {
    argumentIds match {
      case singleArgument :: Nil if isList(singleArgument) =>
        introduceOneListArgumentExamples(argumentIds, loader)
      case first :: second :: Nil if isList(first) && isList(second) =>
        introduceTwoListArgumentsExamples(argumentIds, loader)
      case first :: second :: Nil if isInt(first) && isList(second) =>
        introduceExamplesIntList(argumentIds, loader)
      case _ => null
    }
  }

  def introduceExamplesIntList(argumentIds: Seq[leon.purescala.Common.Identifier], loader: LeonLoader) = {

    // list type
    val ct = argumentIds(1).getType.asInstanceOf[ClassType]

    val setSubclasses = loader.directSubclassesMap(ct).map(_.asInstanceOf[CaseClassType].classDef)

    val (nilClassSet, consClassSet) = setSubclasses.partition(_.fieldsIds.size == 0)

    val nilClass = nilClassSet.head
    val consClass = consClassSet.head

    var counter = 10
    def getIntLiteral = { counter += 1; IntLiteral(counter) }
    val intLiteral = IntLiteral(5)

    val list0 = CaseClass(nilClass, Nil)
    val list1 = CaseClass(consClass, IntLiteral(10) :: list0 :: Nil)
    val list32 = CaseClass(consClass, IntLiteral(5) :: CaseClass(consClass, IntLiteral(7) :: list1 :: Nil) :: Nil)

    Map(argumentIds(0) -> IntLiteral(3), argumentIds(1) -> list32) ::
      Map(argumentIds(0) -> IntLiteral(2), argumentIds(1) -> list32) ::
      Map(argumentIds(0) -> IntLiteral(3), argumentIds(1) -> list0) ::
      Map(argumentIds(0) -> IntLiteral(2), argumentIds(1) -> list0) ::
      Map(argumentIds(0) -> IntLiteral(6), argumentIds(1) -> list32) ::
      Map(argumentIds(0) -> IntLiteral(9), argumentIds(1) -> list32) ::
      Nil
  }

  def introduceOneListArgumentExamples(argumentIds: Seq[leon.purescala.Common.Identifier], loader: LeonLoader) = {

    // list type
    val ct = argumentIds(0).getType.asInstanceOf[ClassType]

    val setSubclasses = loader.directSubclassesMap(ct).map(_.asInstanceOf[CaseClassType].classDef)

    val (nilClassSet, consClassSet) = setSubclasses.partition(_.fieldsIds.size == 0)

    val nilClass = nilClassSet.head
    val consClass = consClassSet.head

    var counter = 10
    def getIntLiteral = { counter += 1; IntLiteral(counter) }
    val intLiteral = IntLiteral(5)

    val list0 = CaseClass(nilClass, Nil)
    val list1 = CaseClass(consClass, IntLiteral(10) :: list0 :: Nil)
    val list2s = CaseClass(consClass, IntLiteral(5) :: list1 :: Nil)
    val list2u = CaseClass(consClass, IntLiteral(5) :: list1 :: Nil)
    val list3s = CaseClass(consClass, IntLiteral(5) :: list2s :: Nil)
    val list3u1 = CaseClass(consClass, IntLiteral(5) :: list2u :: Nil)
    val list3u2 = CaseClass(consClass, IntLiteral(15) :: list2s :: Nil)
    val list3u3 = CaseClass(consClass, IntLiteral(15) :: list2u :: Nil)

    for (list <- List(list0, list1, list2s, list2u, list3s, list3u1, list3u2, list3u3))
      yield Map(argumentIds(0) -> list)
  }

  def introduceTwoListArgumentsExamples(argumentIds: Seq[leon.purescala.Common.Identifier], loader: LeonLoader) = {

    loader.hole.getType match {
      case ct: ClassType =>
        val setSubclasses = loader.directSubclassesMap(ct).map(_.asInstanceOf[CaseClassType].classDef)

        val (nilClassSet, consClassSet) = setSubclasses.partition(_.fieldsIds.size == 0)

        val nilClass = nilClassSet.head
        val consClass = consClassSet.head

        var counter = 0
        def getIntLiteral = { counter += 1; IntLiteral(counter) }

        val list0 = () => CaseClass(nilClass, Nil)
        val list1 = () => CaseClass(consClass, getIntLiteral :: list0() :: Nil)
        val list2 = () => CaseClass(consClass, getIntLiteral :: list1() :: Nil)
        val list3 = () => CaseClass(consClass, getIntLiteral :: list2() :: Nil)
        val list4 = () => CaseClass(consClass, getIntLiteral :: list3() :: Nil)

        val lists = List(list0, list1, list2, list3 /*, list4*/ )

        for (l1 <- lists; l2 <- lists)
          yield Map(argumentIds(0) -> l1(), argumentIds(1) -> l2())

      case _ =>
        null
    }
  }

  def isList(id: Identifier) = id.getType.toString == "List"
  def isInt(id: Identifier) = id.getType == Int32Type

  //  def introduceOneListArgumentExamples(argumentIds: Seq[leon.purescala.Common.Identifier], loader: LeonLoader) = {
  //    
  //    // list type
  //    val ct = argumentIds(0).getType.asInstanceOf[ClassType]
  //    
  //		val setSubclasses = loader.directSubclassesMap(ct).map(_.asInstanceOf[CaseClassType].classDef)
  //		
  //		val (nilClassSet, consClassSet) = setSubclasses.partition(_.fieldsIds.size == 0)
  //		
  //		val nilClass = nilClassSet.head
  //		val consClass = consClassSet.head
  //		
  //		var counter = 10
  //		def getIntLiteral = { counter+=1; IntLiteral(counter) }
  //		val intLiteral = IntLiteral(5)
  //		
  //		val list0 = CaseClass(nilClass, Nil)
  //		val list1 = CaseClass(consClass, IntLiteral(5) :: list0 :: Nil)
  //		val list2 = CaseClass(consClass, IntLiteral(3) :: list1 :: Nil)
  //		val list3 = CaseClass(consClass, IntLiteral(1) :: list2 :: Nil)
  //		val list32 = CaseClass(consClass, IntLiteral(10) :: CaseClass(consClass, IntLiteral(7) :: list1 :: Nil) :: Nil)
  //		
  //		val lists = List(list0, list1, list2, list3, list32)
  //		
  //		for(l1 <- lists)
  //      yield Map(argumentIds(0) -> l1)
  //    
  //  }  
}