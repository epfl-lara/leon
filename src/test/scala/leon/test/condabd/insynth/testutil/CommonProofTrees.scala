package leon.test.condabd.insynth.testutil

import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

import org.junit.Assert._
import org.junit.Test
import org.junit.Ignore

import leon.synthesis.condabd.insynth.leon.query.{ LeonQueryBuilder => QueryBuilder, _ }
import insynth.structures._

import leon.purescala.TypeTrees._
import leon.purescala.Trees._

object CommonProofTrees {

  import CommonDeclarations._

  def exampleBoolToInt = {
    val queryBuilder = new QueryBuilder(Int32Type)

    val query = queryBuilder.getQuery

    val queryDeclaration = query.getDeclaration

    val getBooleanNode =
      new SimpleNode(
        List(booleanDeclaration),
        MutableMap.empty)

    val getIntNode =
      new SimpleNode(
        List(functionBoolToIntDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Boolean") ->
            new ContainerNode(
              MutableSet(getBooleanNode))))

    val queryNode =
      new SimpleNode(
        List(queryDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Int") ->
            new ContainerNode(
              MutableSet(getIntNode))))

    (queryNode, query)
  }

  def exampleIntToInt = {
    val queryBuilder = new QueryBuilder(Int32Type)

    val query = queryBuilder.getQuery

    val queryDeclaration = query.getDeclaration

    val intNode =
      new SimpleNode(
        List(intDeclaration),
        MutableMap.empty)

    val getIntNode =
      new SimpleNode(
        List(functionIntToIntDeclaration),
        MutableMap())

    getIntNode.getParams +=
      (
        Const("Int") ->
        new ContainerNode(
          MutableSet(intNode, getIntNode)))

    val queryNode =
      new SimpleNode(
        List(queryDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Int") ->
            new ContainerNode(
              MutableSet(getIntNode))))

    queryNode
  }
  
  
  def exampleIntToIntBool = {
    val queryBuilder = new QueryBuilder(Int32Type)

    val query = queryBuilder.getQuery

    val queryDeclaration = query.getDeclaration
                    
    val getBooleanNode =
      new SimpleNode(
        List(booleanDeclaration),
        MutableMap.empty)

    val getIntNodeFromBoolean =
      new SimpleNode(
        List(functionBoolToIntDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Boolean") ->
            new ContainerNode(
              MutableSet(getBooleanNode))))

    val getIntNodeFromIntToInt =
      new SimpleNode(
        List(functionIntToIntDeclaration),
        MutableMap())

    getIntNodeFromIntToInt.getParams +=
      (
        Const("Int") ->
        new ContainerNode(
          MutableSet(getIntNodeFromBoolean, getIntNodeFromIntToInt)))

    val queryNode =
      new SimpleNode(
        List(queryDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Int") ->
            new ContainerNode(
              MutableSet(getIntNodeFromBoolean, getIntNodeFromIntToInt))))

    queryNode
  }
  
  
  def exampleIntToIntBoth = {
    val queryBuilder = new QueryBuilder(Int32Type)

    val query = queryBuilder.getQuery

    val queryDeclaration = query.getDeclaration
        
    val intNode =
      new SimpleNode(
        List(intDeclaration),
        MutableMap.empty)
                    
    val getBooleanNode =
      new SimpleNode(
        List(booleanDeclaration),
        MutableMap.empty)

    val getIntNodeFromBoolean =
      new SimpleNode(
        List(functionBoolToIntDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Boolean") ->
            new ContainerNode(
              MutableSet(getBooleanNode))))

    val getIntNodeFromIntToInt =
      new SimpleNode(
        List(functionIntToIntDeclaration),
        MutableMap())

    getIntNodeFromIntToInt.getParams +=
      (
        Const("Int") ->
        new ContainerNode(
          MutableSet(intNode, getIntNodeFromBoolean, getIntNodeFromIntToInt)))

    val queryNode =
      new SimpleNode(
        List(queryDeclaration),
        MutableMap( // for each parameter type - how can we resolve it
          Const("Int") ->
            new ContainerNode(
              MutableSet(getIntNodeFromBoolean, getIntNodeFromIntToInt))))

    queryNode
  }
  
  // TODO do if we need abstraction (high-order functions)
//  def exampleFunctionIntToInt = {
//    val queryBuilder = new QueryBuilder(FunctionType(List(Int32Type), Int32Type))
//
//    val query = queryBuilder.getQuery
//
//    val queryDeclaration = query.getDeclaration
//                    
//    val getBooleanNode =
//      new SimpleNode(
//        List(booleanDeclaration),
//        MutableMap.empty)
//
//    val getIntNodeFromBoolean =
//      new SimpleNode(
//        List(functionBoolToIntDeclaration),
//        MutableMap( // for each parameter type - how can we resolve it
//          Const("Boolean") ->
//            new ContainerNode(
//              MutableSet(getBooleanNode))))
//
//    val getIntNodeFromIntToInt =
//      new SimpleNode(
//        List(functionIntToIntDeclaration),
//        MutableMap())
//
//    getIntNodeFromIntToInt.getParams +=
//      (
//        Const("Int") ->
//        new ContainerNode(
//          MutableSet(getIntNodeFromBoolean, getIntNodeFromIntToInt)))
//
//    val queryNode =
//      new SimpleNode(
//        List(queryDeclaration),
//        MutableMap( // for each parameter type - how can we resolve it
//          Const("Int") ->
//            new ContainerNode(
//              MutableSet(getIntNodeFromBoolean, getIntNodeFromIntToInt))))
//
//    queryNode
//  }

}