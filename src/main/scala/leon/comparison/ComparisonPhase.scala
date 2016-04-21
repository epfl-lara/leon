package leon.comparison

import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.{ExprOps, Expressions}
import leon.purescala.Expressions.{Let, MatchExpr, Passes, Variable, _}

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  val print = true

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    if (print)
      println("--------------")
      println("APPLY METHOD OF COMPARISONPHASE")
      println("--------------")

      println("--------------")
      println("FUNDEFS BASE")
      println("--------------")

    val comparisonBase = ComparisonBase(ctx, "testcases/comparison/base")
    val listFunDef_base = comparisonBase.listFunDef
    if (print) listFunDef_base.map(println(_))

    if (print)
      println("--------------")
      println("FUNDEFS TO-COMPARE")
      println("--------------")

    val listFunDef = getFunDef(ctx, program)
    if (print) listFunDef.map(println(_))


    val compared = compare(listFunDef_base, listFunDef)




    ComparisonReport(comparisonBase, program, compared)
  }


  /**
    * This is the core of the phase, where each given function will be compared to the comparison bases FunDefs,
    * two by two
    *
    * @param FunDefs_base
    * @param FunDefs
    * @return
    */
  def compare(FunDefs_base: List[FunDef], FunDefs: List[FunDef]): List[(FunDef, FunDef, Double)] = {

    if (print)
      println("--------------")
      println("COMPARISON")
      println("--------------")

    // store all the similar function we find, between base and to-compare programs
    // later we will add some extra information (which part or which percentage is equal)
    val pairEqualFunDef =
      for{
        funDef <- FunDefs
        funDef_base <- FunDefs_base
        percentageSimilarity = recursiveSearch(funDef_base.body.get, funDef.body.get)
        if(percentageSimilarity > 0.0)
      } yield {
        (funDef, funDef_base, percentageSimilarity)
      }

    pairEqualFunDef
  }


  def isMatchExprExlusive(matchCases: Seq[MatchCase]): Boolean = {
    val instanceOf= matchCases.filter(_.pattern.isInstanceOf[InstanceOfPattern])
    true
  }


  /**
    * Determine if the match/case function we compare is a Pattern Match instead of a Value Match
    *
    * We want to compare match/case function in two different way, Pattern Matching or Value Matching (the fact of
    * using match/case as a replacement of if/else).
    *
    * @param cases_base
    * @param cases
    * @return
    */
  def arePatternMatch(cases_base: Seq[MatchCase], cases: Seq[MatchCase]): Boolean =
    isPatternMatch(cases_base) && isPatternMatch(cases)


  def isPatternMatch(cases: Seq[MatchCase]): Boolean = {
    val filteredSeq = cases.filter(p =>
      p.pattern.isInstanceOf[InstanceOfPattern] ||
      p.pattern.isInstanceOf[CaseClassPattern])

    filteredSeq.nonEmpty
  }

  def extractPatternMatchMap(cases_base: Seq[MatchCase]) = {
    println("it is a patternMatchCase")
    cases_base.map(a => a.pattern match {
      case InstanceOfPattern(_, ct) => (ct.getType -> a.rhs)
      case CaseClassPattern(_, ct, _) => (ct.getType -> a.rhs)
      case _ => null
    }).toMap
  }


  /**
    * For the moment: default case
    *
    * @param cases_base
    * @param cases
    * @return
    */
  def isValueMatch(cases_base: Seq[MatchCase], cases: Seq[MatchCase]): Boolean = true

  def extractValueMatchMap(cases_base: Seq[MatchCase]) = {
    cases_base.map(a => a.pattern -> a.rhs).toMap
  }

  // IDEE: comparer les types plutôt que les pattern complet des match case, et éventuellement oublié les optGuard
  def compareExpr(expr_base: Expr, expr: Expr): Boolean = {
    val expr_base_norm = ExprOps.normalizeStructure(expr_base)._1
    val expr_norm = ExprOps.normalizeStructure(expr)._1

  println("type of expression: ")
  println(expr_base_norm, expr_base_norm.getType, expr_base_norm.isInstanceOf[MatchExpr])
  println(expr_norm, expr_norm.getType, expr_norm.isInstanceOf[MatchExpr])

    (expr_base_norm, expr_norm) match {
      case (MatchExpr(_, cases_base), MatchExpr(_, cases)) if arePatternMatch(cases_base, cases) =>
        println("YOU ARE HERE !!")
        val map_case_base = extractPatternMatchMap(cases_base)
        val map_case = extractPatternMatchMap(cases)
        if (print) {
          println("Map Match Expr")
          println(map_case_base)
          println(map_case)
        }
        map_case_base == map_case

      case (MatchExpr(_, cases_base), MatchExpr(_, cases)) if isValueMatch(cases_base, cases) =>
        val map_case_base = extractValueMatchMap(cases_base)
        val map_case = extractValueMatchMap(cases)
        if (print) {
          println("Map Match Expr")
          println(map_case_base)
          println(map_case)
        }
        map_case_base == map_case
      case _ =>
        expr_base_norm == expr_norm
    }
  }

  def recursiveSearch(expr_base: Expr, expr: Expr): Double = {
    if (print)
      println("--------------")
      println("COMPARE EXPR")
      println("--------------")
      println("original base expression : ")
      println(expr_base)
      println("original expression : ")
      println(expr)

    val listExpr_base = treeToList(expr_base)
    val listExpr = treeToList(expr)

    if (print)
      println("list base expr")
      println(listExpr_base.size, listExpr_base)
      println("list expr")
      println(listExpr.size, listExpr)

    val similarExprList = for{
      expr_base <- listExpr_base
      expr <- listExpr
      if (compareExpr(expr_base, expr))
    } yield {
      (expr_base, expr)
    }


    if (print)
      println("similar Expr List")
      println(similarExprList)

    val percentageSimilarity =
      similarExprList.size.toDouble / listExpr_base.size.toDouble

    percentageSimilarity
  }


  def treeToList(expr: Expr): List[Expr] = {
    val list: List[Expr] = expr match {
      case Let(binder, value, body) => List(expr) ++ treeToList(body)

      // we don't list the scrutinee. Why? Because as it will be normalized later, a unique identifier
      // will ALWAYS be the same.
      case MatchExpr(scrutinee, cases) =>
        List (expr)  ++ cases.flatMap(m => m.expressions.flatMap(e => treeToList(e)))

      //default value for any non-handled expression
      case x if x.isInstanceOf[Expr] => List(x)

      //default value for error handling, should never reach that
      case _ => Nil
    }

    list
  }

/*  def treeToListExemple(expr: Expr) = {
    val normalized = postMap {
      case Lambda(args, body) => Some(Lambda(args.map(vd => vd.copy(id = subst(vd.id))), body))
      case Forall(args, body) => Some(Forall(args.map(vd => vd.copy(id = subst(vd.id))), body))
      case Let(i, e, b)       => Some(Let(subst(i), e, b))
      case MatchExpr(scrut, cses) => Some(MatchExpr(scrut, cses.map { cse =>
        cse.copy(pattern = replacePatternBinders(cse.pattern, subst))
      }))
      case Passes(in, out, cses) => Some(Passes(in, out, cses.map { cse =>
        cse.copy(pattern = replacePatternBinders(cse.pattern, subst))
      }))
      case Variable(id) => Some(Variable(subst(id)))
      case _ => None
    } (expr)

    normalized
  }*/


  def compareFunDef(f1: FunDef, f2: FunDef): Boolean = {

    println("f1 : ", f1.body.toString())
    println("f2 : ", f2.body.toString())

    val (normalizedBody1, map1) = ExprOps.normalizeStructure(f1.body.get)
    val (normalizedBody2, map2) = ExprOps.normalizeStructure(f2.body.get)

    println("normalizedBody1 : ", normalizedBody1, map1)
    println("normalizedBody2 : ", normalizedBody2, map2)

    if (normalizedBody1 == normalizedBody2) {
      println("true")
      true
    }
    else {
      println("false")
      false
    }
  }

  /**
    * This method derives from VerificationPhase
    * Extract the list of function defined in a program
    * */
  def getFunDef(ctx : LeonContext, program: Program): List[FunDef] = {
    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"
    val filterFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)
    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }
    program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)
  }
}
