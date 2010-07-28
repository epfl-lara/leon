package setconstraints

import scala.collection.mutable.{Map, HashMap, ListBuffer}

import purescala.Definitions._
import purescala.Trees.{And => _, Equals => _, _}
import purescala.Common.Identifier
import purescala.TypeTrees.ClassType


import Trees._

object CnstrtGen {
  
  def apply(pgm: Program,
                typeVars: Map[ClassTypeDef, VariableType],
                funVars: Map[FunDef, (Seq[VariableType], VariableType)],
                cl2adt: Map[ClassTypeDef, SetType]
              ): Formula = {

    val funCallsCnstr: ListBuffer[Relation] = new ListBuffer[Relation]()
    val patternCnstr: ListBuffer[Relation] = new ListBuffer[Relation]()

    def cnstrExpr(expr: Expr, context: Map[Identifier, VariableType]): (SetType, Seq[Relation]) = expr match {
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
        val (tArgs,rt) = funVars(fd)
        tArgs.zip(args).foreach{case (v, expr) => {
            val (newT, newCnstr) = cnstrExpr(expr, context)
            funCallsCnstr ++= newCnstr
            funCallsCnstr += Include(newT, v)
          }
        }
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
        subConsType.zip(ccd.fields)foreach{case (t, vd) => patternCnstr += Equals(t, cl2adt(vd.tpe.asInstanceOf[ClassType].classDef))} //TODO bug if there are nested pattern
        (ConstructorType(ccd.id.name, subConsType), newMap)
      }
    }

    def cnstrFun(fd: FunDef): Seq[Relation] = {
      val argsT = funVars(fd)._1
      val argsID = fd.args.map(vd => vd.id)
      val context = argsID.zip(argsT).foldLeft(Map[Identifier, VariableType]())((acc, el) => acc + el)
      val (bodyType, cnstrts) = cnstrExpr(fd.body.get, context)
      cnstrts :+ Include(bodyType, funVars(fd)._2)
    }

    def cnstrTypeHierarchy(pgm: Program): Seq[Relation] = {
      val caseClasses = pgm.definedClasses.filter(_.isInstanceOf[CaseClassDef])
      caseClasses.map(cc => Include(cl2adt(cc), cl2adt(cc.parent.get)))
    }

    val cnstrtsTypes = cnstrTypeHierarchy(pgm)

    println(typeVars)
    println(cnstrtsTypes)

    val funs = pgm.definedFunctions
    val cnstrtsFunctions = funs.flatMap(cnstrFun)

    And(cnstrtsTypes ++ cnstrtsFunctions ++ funCallsCnstr ++ patternCnstr)
  }

}
