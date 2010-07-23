package setconstraints

import scala.collection.mutable.{Map, HashMap, ListBuffer}

import purescala.Definitions._
import purescala.Trees.{And => _, _}
import purescala.Common.Identifier


import Trees._

object CnstrtGen {
  
  def apply(pgm: Program,
                typeVars: Map[ClassTypeDef, VariableType],
                funVars: Map[FunDef, (Seq[VariableType], VariableType)],
                cl2adt: Map[ClassTypeDef, SetType]
              ): Formula = {

    val funCallsCnstr: ListBuffer[Include] = new ListBuffer[Include]()
    val patternCnstr: ListBuffer[Include] = new ListBuffer[Include]()

    def addFunCallCnst(fi: FunctionInvocation) {
      val (args,_) = funVars(fi.funDef)
      args.zip(fi.args).foreach{case (v, expr) => {
          val (newT, newCnstr) = cnstrExpr(expr, Map())
          funCallsCnstr ++= newCnstr
          funCallsCnstr += Include(v, newT)
        }
      }
    }

    def cnstrExpr(expr: Expr, context: Map[Identifier, VariableType]): (SetType, Seq[Include]) = expr match {
      case Variable(id) => {
        (context(id), Seq())
      }
      case IfExpr(cond, then, elze) => {
        val (tType, tCnstrs) = cnstrExpr(then, context)
        val (eType, eCnstrs) = cnstrExpr(elze, context)
        (UnionType(Seq(tType, eType)), tCnstrs ++ eCnstrs)
      }
      case MatchExpr(scrut, cases) => {
        val (sType, sCnstrs) = cnstrExpr(scrut, context)
        val (cType, cCnstrs) = cases.map(mc => {
          //val theGuard = mc.theGuard
          val rhs = mc.rhs
          val (pt, pvc) = pattern2Type(mc.pattern)
          cnstrExpr(rhs, context ++ pvc)
        }).unzip
        val mType = freshVar("match")
        val mCnstrs = cType.map(t => Include(t, mType))
        (mType, mCnstrs ++ cCnstrs.flatMap(x => x))
      }
      case FunctionInvocation(fd, args) => {
        val rt = funVars(fd)._2
        (rt, Seq())
      }
      case CaseClass(ccd, args) => {
        val (argsType, cnstrts) = args.map(e => cnstrExpr(e, context)).unzip
        (ConstructorType(ccd.id.name, argsType), cnstrts.flatMap(x => x))
      }
      case _ => error("Not yet supported: " + expr)
    }

    def pattern2Type(pattern: Pattern): (SetType, Map[Identifier, VariableType]) = pattern match {
      case InstanceOfPattern(binder, ctd) => error("not yet supported")
      case WildcardPattern(binder) => {
        val v = freshVar(binder match {case Some(id) => id.name case None => "x"})
        (v, binder match {case Some(id) => Map(id -> v) case None => Map()})
      }
      case CaseClassPattern(binder, ccd, sps) => {
        val (subConsType, subVarType) = sps.map(p => pattern2Type(p)).unzip
        val newMap = subVarType.foldLeft(Map[Identifier, VariableType]())((acc, el) => acc ++ el)
        (ConstructorType(ccd.id.name, subConsType), newMap)
      }
    }

    def cnstrFun(fd: FunDef): Seq[Include] = {
      val argsT = funVars(fd)._1
      val argsID = fd.args.map(vd => vd.id)
      val context = argsID.zip(argsT).foldLeft(Map[Identifier, VariableType]())((acc, el) => acc + el)
      val (bodyType, cnstrts) = cnstrExpr(fd.body.get, context)
      cnstrts :+ Include(funVars(fd)._2, bodyType)
    }

    def cnstrTypeHierarchy(pgm: Program): Seq[Include] = {
      val caseClasses = pgm.definedClasses.filter(_.isInstanceOf[CaseClassDef])
      caseClasses.map(cc => Include(cl2adt(cc), cl2adt(cc.parent.get)))
    }

    val cnstrtsTypes = cnstrTypeHierarchy(pgm)

    val funs = pgm.definedFunctions
    val cnstrtsFunctions = funs.flatMap(cnstrFun)

    And(cnstrtsTypes ++ cnstrtsFunctions)
  }

}
