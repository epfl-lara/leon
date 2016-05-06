package leon.comparison

import leon.purescala.Definitions.{CaseClassDef, ClassDef}
import leon.purescala.Expressions._
import leon.purescala.Types.{ClassType, TypeTree}

/**
  * Created by joachimmuth on 25.04.16.
  */
object Utils {


  /**
    * One hard piece is to compare two case clase, because it cannot be normalized like value
    *
    * @return
    */

  def compareClassDef(classA: ClassDef, classB: ClassDef): Double = {
    (classA, classB) match {
      case (a,b) if (a.isAbstract && b.isAbstract) =>
        if (a.knownCCDescendants.size == b.knownCCDescendants.size) 1.0
        else 0.0
      case (a: CaseClassDef, b:CaseClassDef) =>
        compareCaseClassDef(a,b)
      case _ =>   0.0

    }
  }

  def compareTypeTree(typeA: TypeTree, typeB: TypeTree): Double = (typeA, typeB) match {
    case (a: ClassType, b: ClassType) => compareClassDef(a.classDef, b.classDef)
    case _ => 0.0
  }


  /**
    * Combine number of parameter, of parameter of its own type and of the type of its parent
    * (to be improved for CaseClass without argument, for example match with parent)
    *
    * @param a
    * @param b
    * @return
    */
  def compareCaseClassDef(a: CaseClassDef, b: CaseClassDef): Double = {
    val ownTypeA: Int = argumentsOfOwnType(a)
    val ownTypeB: Int = argumentsOfOwnType(b)
    val parentTypeA : Int = argumentsOfParentType(a)
    val parentTypeB: Int = argumentsOfParentType(b)

    val percentageMatch: Double = percent(a.fields.size, b.fields.size) *
      percent(ownTypeA, ownTypeB) * percent(parentTypeA, parentTypeB)

    percentageMatch
  }


  /**
    * Count how many occurrences of its own type appear in its arguments
    * (to be improved if multiples types)
    *
    * @param a the case class
    * @return
    */
  def argumentsOfOwnType(a: CaseClassDef): Int = {
    a.fields.map(_.getType).count(a.tparams.map(_.tp.getType).contains(_))
  }

  /**
    * Count how many occurrences of its parent type appear in its arguments
    *
    * @param a
    * @return
    */
  def argumentsOfParentType(a: CaseClassDef): Int = a match {
    case _ if a.hasParent => a.fields.map(_.getType).count(_ == a.parent.get.getType)
    case _ => 0
  }

  def percent(a: Int, b: Int): Double = {
    if(a == 0 && b == 0) 1.0
    else if (a == 0 || b == 0) 0.0
    else Math.min(a.toDouble/b.toDouble, b.toDouble/a.toDouble)
  }

  def percentBetweenTwo(a: Int, option1: Int, option2: Int): Double =
    Math.min(percent(a, option1), percent(a, option2))

  def mean(a: Double): Double = a
  def mean(a: Double, b: Double): Double = (a + b) / 2
  def mean(a: Double, b: Double, c: Double): Double = (a + b + c) / 3
  def mean(a: Double, b: Double, c: Double, d: Double): Double = (a + b + c + d) / 4
  def mean(list : List[Double]): Double = list.foldLeft(0.0)(_+_) / list.size.toDouble


  /**
    * Main function allowing to traverse a tree. This function is made in a way to be the more generic possible,
    * letting choose how we deal with the parent (the current Expr) and its children.
    *
    * The function "collect" derives from it, by choosing "onChild" to be a recursive call.
    * The function "getChild" also derives from it, by doing nothing with the parent and adding the children to the
    * list, but without recursion.
    *
    * As we can see, this function allow to do a lot of things and can be used in the future to test new configuration
    *
    * @param expr the parent of the tree we want to traverse. Never forget, we use the term "parent" but expr contains
    *             all the tree
    * @param onParent function applied to this parent. It can neglect it (expr => Nil), store it (expr => List(expr))
    *                 or store one of its parameter (expr => List(expr.getClass))
    * @param onChild function applied to the children expression of "expr". It can be recursive (as in "collect"
    *                function) or can store some information about it (as in "getChildren)
    * @tparam T the type of the returned list we want to get after traversing the tree
    * @return a list containing all the chosen values stored by both function "onParent" and "onChildren"
    */
  def traverse[T](expr: Expr)(onParent: Expr => List[T])(onChild: Expr => List[T]): List[T] = expr match {
    case Require(pred, body) => onParent(expr) ++ onChild(pred) ++ onChild(body)
    case Ensuring(body, pred) => onParent(expr) ++ onChild(body) ++ onChild(pred)
    case Assert(pred, _, body) => onParent(expr) ++ onChild(pred) ++ onChild(body)
    case Let(binder, value, body) => onParent(expr) ++ onChild(value) ++ onChild(body)

    // how to handle fds (function definition) ??
    case LetDef(fds, body) => onParent(expr) ++ onChild(body)

    case Application(callee, args) => onParent(expr) ++ onChild(callee) ++ args.flatMap(onChild(_))
    case Lambda(_, body) => onParent(expr) ++ onChild(expr)
    case Forall(_, body) => onParent(expr) ++ onChild(body)
    case FunctionInvocation(_ ,args) =>
      onParent(expr) ++ args.flatMap(onChild(_))
    case IfExpr(cond, thenn, elze) => onParent(expr) ++ onChild(cond) ++ onChild(thenn) ++ onChild(elze)

    // we don't list the scrutinee
    // method cases.expression return both optGuard and rhs
    case MatchExpr(scrutinee, cases) =>
      onParent(expr)  ++ cases.flatMap(m => m.expressions.flatMap(e => onChild(e)))

    case CaseClass(_, args) => onParent(expr) ++ args.flatMap(onChild(_))
    case CaseClassSelector(_, caseClass, _) =>
      onParent(expr) ++ onChild(caseClass)
    case Equals(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)

    /* Propositional logic */
    case And(exprs) =>
      onParent(expr) ++ exprs.flatMap(onChild(_))
    case Or(exprs) =>
      onParent(expr) ++ exprs.flatMap(onChild(_))
    case Implies(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case Not(argExpr) =>
      onParent(expr) ++ onChild(argExpr)

    case IsInstanceOf(argExpr, _) =>
      onParent(expr) ++ onChild(argExpr)
    case AsInstanceOf(argExpr, _) =>
      onParent(expr) ++ onChild(argExpr)

    /* Integer arithmetic */
    case Plus(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case Minus(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case UMinus(argExpr) =>
      onParent(expr) ++ onChild(argExpr)
    case Times(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case Division(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case Remainder(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case Modulo(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case GreaterThan(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case GreaterEquals(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case LessThan(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case LessEquals(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)

    /* Real arithmetic */
    case RealPlus(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case RealMinus(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case RealDivision(lhs, rhs) =>
      onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case RealTimes(lhs, rhs) => onParent(expr) ++ onChild(lhs) ++ onChild(rhs)
    case RealUMinus(argExpr) =>
      onParent(expr) ++ onChild(argExpr)

    /* Tuple operations */
    case Tuple(exprs) => onParent(expr) ++ exprs.flatMap(onChild(_))
    case TupleSelect(tuple, _) =>
      onParent(expr) ++ onChild(tuple)

    /* Set operations */
    case FiniteSet(elements, _ ) => onParent(expr) ++ elements.flatMap(onChild(_))
    case ElementOfSet(element, set) =>
      onParent(expr) ++ onChild(element) ++ onChild(set)
    case SetCardinality(set) => onParent(expr) ++ onChild(set)
    case SubsetOf(set1, set2) => onParent(expr) ++ onChild(set1) ++ onChild(set2)
    case SetIntersection(set1, set2) =>
      onParent(expr) ++ onChild(set1) ++ onChild(set2)
    case SetUnion(set1, set2) =>
      onParent(expr) ++ onChild(set1) ++ onChild(set2)
    case SetDifference(set1, set2) => onParent(expr) ++ onChild(set1) ++ onChild(set2)

    /* Map operations */
    case FiniteMap(pairs, _, _) =>
      onParent(expr) ++ pairs.toList.flatMap(t => onChild(t._1) ++ onChild(t._2))
    case MapApply(map, key) => onParent(expr) ++ onChild(map) ++ onChild(key)
    case MapUnion(map1, map2) => onParent(expr) ++ onChild(map1) ++ onChild(map2)
    case MapDifference(map, keys) => onParent(expr) ++ onChild(map) ++ onChild(keys)
    case MapIsDefinedAt(map, key) => onParent(expr) ++ onChild(map) ++ onChild(key)

    /* Array operations */
    case ArraySelect(array, index) => onParent(expr) ++ onChild(array) ++ onChild(index)
    case ArrayUpdated(array, index, newValue) =>
      onParent(expr) ++ onChild(array) ++ onChild(index) ++ onChild(newValue)
    case ArrayLength(array) => onParent(expr) ++ onChild(array)
    case NonemptyArray(elems, defaultLength) => onParent(expr) ++ elems.flatMap(t => onChild(t._2))
    case EmptyArray(_) => onParent(expr)




    // default value for any easy-to-handled or Terminal expression
    // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
    // leave aside (at least for the moment): String Theory, BitVector Operation, Special trees for synthesis (holes, ...)
    case x if x.isInstanceOf[Expr] => onParent(expr)

    //default value for error handling, should never reach that
    case _ => Nil
  }


  /**
    * Derived from "traverse" function. Traverse all the tree and collect whished information about Expr composing it.
    * It fixes the "onChildren" function to be recursive and let the "onParent" be the one deciding what information
    * will be stored
    *
    * collectExpr and collectClass collect respectively the Expr and the Class of each element of the tree.
    *
    * BEWARE: Expr are complete trees even if we call it "parent". When we compare two Expr, we compare two entire tree.
    * At the contrary, when we compare to Class, we lose this information and only compare the Class of two parent.
    * @param expr
    * @param f
    * @tparam T
    * @return
    */
  def collect[T](expr: Expr)(f:Expr => List[T]): List[T] = traverse(expr)(f)(expr => collect(expr)(f))

  def collectClass(expr: Expr): List[Class[_ <: Expr]] =
    collect[Class[_ <: Expr]](expr) (expr => List(expr.getClass))

  def collectExpr(expr: Expr): List[Expr] =
    collect[Expr](expr) (expr => List(expr))

  /**
    * Give a list of all children of one parent. Why do we need to use "traverse" function to get them? Because
    * there is a lot of possible CaseClass extending Expr, and we want to deal with any of them.
    * @param expr
    * @return
    */
  def getChild(expr: Expr): List[Expr] =
    traverse(expr) (expr => Nil) (expr => List(expr))


}
