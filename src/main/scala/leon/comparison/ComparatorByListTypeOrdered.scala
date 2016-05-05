package leon.comparison

import leon.purescala.Expressions._

/**
  * Created by joachimmuth on 05.05.16.
  *
  * In contrary of the comparator by List of Expressions, in which each Expr contains its whole tree of children,
  * when we compare type of Expressions between them, we loose the information about children.
  *
  * This is a variation of ComparatorByListType where we check what is the longest sequence of same type.
  *
  */
object ComparatorByListTypeOrdered {
  val name: String = "byListTypeOrdered"

  def compare(expr_base: Expr, expr: Expr): Double = {
    val similarTypeTree: Int = biggestSimilarTypeTree(expr_base, expr)


    val listClassesB = ComparatorByListType.treeToList(expr_base)
    val listClasses = ComparatorByListType.treeToList(expr)


    Utils.percentBetweenTwo(similarTypeTree, listClassesB.size, listClasses.size)
  }


  def biggestSimilarTypeTree(expr_base: Expr, expr: Expr): Int = {
    def similarTypeTree(exprB: Expr, expr: Expr, acc: Int) = 0
  0
  }



  /**
    * This function help to "traverse" a tree, tak
    * @param expr the parent expression
    * @return a sequence of all his direct children, most of time 1, 0 if it is a leaf.
    */
  def getChildren(expr: Expr): Seq[Expr] = expr match {
    case Require(pred, body) => Seq(pred, body)
    case Ensuring(body, pred) => Seq(body, pred)
    case Assert(pred, _, body) => Seq(pred, body)
    case Let(binder, value, body) => Seq(value, body)

    // how to handle fds (function definition) ??
    case LetDef(fds, body) => Seq(body)

    case Application(callee, args) => callee +: args
    case Lambda(_, body) => Seq(body)
    case Forall(_, body) => Seq(body)
    case FunctionInvocation(_ ,args) => args
    case IfExpr(cond, thenn, elze) => Seq(cond, thenn, elze)

    // we don't list the scrutinee
    // method cases.expression return both optGuard and rhs
    case MatchExpr(scrutinee, cases) => scrutinee +: cases.flatMap(_.expressions)

    case CaseClass(_, args) => args
    case CaseClassSelector(_, caseClass, _) => Seq(caseClass)
    case Equals(lhs, rhs) => Seq(lhs, rhs)

    /* Propositional logic */
    case And(exprs) => exprs
    case Or(exprs) => exprs
    case Implies(lhs, rhs) => Seq(lhs, rhs)
    case Not(argExpr) => Seq(argExpr)

    case IsInstanceOf(argExpr, _) => Seq(argExpr)
    case AsInstanceOf(argExpr, _) => Seq(argExpr)

    /* Integer arithmetic */
    case Plus(lhs, rhs) => Seq(lhs, rhs)
    case Minus(lhs, rhs) => Seq(lhs, rhs)
    case UMinus(argExpr) => Seq(argExpr)
    case Times(lhs, rhs) => Seq(lhs, rhs)
    case Division(lhs, rhs) => Seq(lhs, rhs)
    case Remainder(lhs, rhs) => Seq(lhs, rhs)
    case Modulo(lhs, rhs) => Seq(lhs, rhs)
    case GreaterThan(lhs, rhs) => Seq(lhs, rhs)
    case GreaterEquals(lhs, rhs) => Seq(lhs, rhs)
    case LessThan(lhs, rhs) => Seq(lhs, rhs)
    case LessEquals(lhs, rhs) => Seq(lhs, rhs)

    /* Real arithmetic */
    case RealPlus(lhs, rhs) => Seq(lhs, rhs)
    case RealMinus(lhs, rhs) => Seq(lhs, rhs)
    case RealDivision(lhs, rhs) => Seq(lhs, rhs)
    case RealTimes(lhs, rhs) => Seq(lhs, rhs)
    case RealUMinus(argExpr) => Seq(argExpr)

    /* Tuple operations */
    case Tuple(exprs) => exprs
    case TupleSelect(tuple, _) => Seq(tuple)

    /* Set operations */
    case FiniteSet(elements, _ ) => elements.toSeq
    case ElementOfSet(element, set) => Seq(element, set)
    case SetCardinality(set) =>  Seq(set)
    case SubsetOf(set1, set2) => Seq(set1, set2)
    case SetIntersection(set1, set2) => Seq(set1, set2)
    case SetUnion(set1, set2) => Seq(set1, set2)
    case SetDifference(set1, set2) => Seq(set1, set2)

    /* Map operations */
    case FiniteMap(pairs, _, _) => pairs.toSeq.flatMap(p => Seq(p._1, p._2))
    case MapApply(map, key) => Seq(map, key)
    case MapUnion(map1, map2) => Seq(map1, map2)
    case MapDifference(map, keys) => Seq(map, keys)
    case MapIsDefinedAt(map, key) => Seq(map, key)

    /* Array operations */
    case ArraySelect(array, index) => Seq(array, index)
    case ArrayUpdated(array, index, newValue) => Seq(array, index, newValue)
    case ArrayLength(array) => Seq(array)
    case NonemptyArray(elems, defaultLength) => elems.map(t => t._2).toSeq
    case EmptyArray(_) => Nil

    // default value for any easy-to-handled or Terminal expression
    // including: NoTree, Error, Variable, MethodInvocation, This, all Literal, ConverterToString
    // leave aside (at least for the moment): String Theory, BitVector Operation, Special trees for synthesis (holes, ...)
    case x if x.isInstanceOf[Expr] => Nil

    //default value for error handling, should never reach that
    case _ => Nil
  }
}
