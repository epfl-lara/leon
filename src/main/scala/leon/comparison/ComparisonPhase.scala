package leon.comparison

import leon.OptionsHelpers._
import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.purescala.Common.Identifier
import leon.{LeonContext, OptionsHelpers, SharedOptions, SimpleLeonPhase}
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.ExprOps
import leon.purescala.Expressions.{Let, MatchExpr, Passes, Variable, _}
import leon.utils.PreprocessingPhase
import leon.verification.VerificationReport

/**
  * Created by joachimmuth on 23.03.16.
  */
object ComparisonPhase extends SimpleLeonPhase[Program, ComparisonReport] {

  override val description: String = "Comparison phase between input program and Leon example suite"
  override val name: String = "Comparison"

  override def apply(ctx: LeonContext, program: Program): ComparisonReport = {
    println("you are in apply method of comparison")
    val listFunDef = getFunDef(ctx, program)


    val listFunDef_base = ComparisonBase(ctx, "testcases/comparison/base").listFunDef


    println("--------------")
    println("PRINT BASE PROG AND COMPARED PROG")
    println("--------------")
    println("listFunDef is : ", listFunDef.toString())
    println("And the first element is : ", listFunDef.tail.head.toString)

    println("--------------")
    println("BASE PROG")
    println("--------------")

    println("tparam compared head is ", listFunDef_base.tail.head.tparams.toString())
    println("param compared head is ", listFunDef_base.tail.head.params.toString())
    println("return compared type is ", listFunDef_base.tail.head.returnType.toString)
    println("body compared head is ", listFunDef_base.tail.head.body.toString)
    println("fullBody compared head is", listFunDef_base.tail.head.fullBody.toString)

    println("--------------")
    println("COMPARED PROG")
    println("--------------")
    println("tparam head is ", listFunDef.tail.head.tparams.toString())
    println("param head is ", listFunDef.tail.head.params.toString())
    println("return type is ", listFunDef.tail.head.returnType.toString)
    println("body head is", listFunDef.tail.head.body.toString)
    println("fullBody head is", listFunDef.tail.head.fullBody.toString)

    val compared = compare(listFunDef_base, listFunDef)

    println(compared.toString())

    ComparisonReport(program, listFunDef)
  }


  /*
  This method derives from VerificationPhase
  It's aim is to extract something from the program (FunDef) to begin working
   */
  def getFunDef(ctx : LeonContext, program: Program): List[FunDef] = {
    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"
    val filterFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)
    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher(program)), Some(excludeByDefault _))
    }
    program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)
  }

  def compare(p1: List[FunDef], p2: List[FunDef]): List[(FunDef, FunDef)] = {

    println("--------------")
    println("COMPARISON")
    println("--------------")
    println("--------------")
    println("GET PRECISE ELEMENT")
    println("--------------")

    val f1 = p1(1)
    val f2 = p2(1)

    println("getType" , f1.body.toList.head.getType.toString)
    println("getPos" , f1.body.toList.head.getPos.toString)
    println("para", f1.params)
    println("defaultValue", f1.params.head.defaultValue)
    println("getType ", f1.params.head.getType)
    println("id", f1.params.head.id)
    println("toVariable", f1.params.map(_.toVariable))
    println(f1.body.toList.map{
      case BVPlus(lhs, rhs) => (lhs, rhs)
    })

    println("--------------")
    println("Normalize plus4")
    println("--------------")

    val (normalizedExp1, map1) = ExprOps.normalizeStructure(f1.body.get)
    val (normalizedExp2, map2) = ExprOps.normalizeStructure(f2.body.get)
    println("normalized structure f1 : ", normalizedExp1, map1)
    println("normalized structure f2 : ", normalizedExp2, map2)

    println("f1.normalized == f2.normalized ", normalizedExp1 == normalizedExp2)

    println("--------------")
    println("Normalize a+b")
    println("--------------")

    val (normalizedExp11, map11) = ExprOps.normalizeStructure(p1(2).body.get)
    val (normalizedExp21, map21) = ExprOps.normalizeStructure(p1(2).body.get)
    println("normalized structure f1 : ", normalizedExp11, map11)
    println("normalized structure f2 : ", normalizedExp21, map21)


    val pairEqualFunDef =
      for{
        f1 <- p1
        f2 <- p2
        if(compareFunDef(f1, f2))
      } yield {
        (f1, f2)
      }

    println("pair FunDef : ", pairEqualFunDef)

    pairEqualFunDef
  }

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

  def treeCrowler(expr: Expr) = {
    expr match {
      case Lambda(args, _) => args.map(_.id)
      case Forall(args, _) => args.map(_.id)
      case LetDef(fds, _) => fds.flatMap(_.paramIds)
      case Let(i, _, _) => Seq(i)
      case MatchExpr(_, cses) => cses.flatMap(_.pattern.binders)
      case Passes(_, _, cses) => cses.flatMap(_.pattern.binders)
      case Variable(id) => Seq(id)
      case _ => Seq.empty[Identifier]
    }
  }
}
