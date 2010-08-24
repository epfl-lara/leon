package setconstraints

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
              ): Set[Relation] = {

    def unzip3[A,B,C](seqs: Seq[(A,B,C)]): (Seq[A],Seq[B],Seq[C]) = 
      seqs.foldLeft((Seq[A](), Seq[B](), Seq[C]()))((a, t) => (t._1 +: a._1, t._2 +: a._2, t._3 +: a._3))

    def cnstrExpr(expr: Expr, context: Map[Identifier, VariableType]): (VariableType, Seq[Relation], Map[Expr, VariableType]) = {
      val exprVarType = freshVar("expr")
      val (rels, e2t) = expr match {
        case Variable(id) => {
          (Seq(Equals(context(id), exprVarType)), Map[Expr, VariableType]())
        }
        case IfExpr(cond, then, elze) => {
          val (tType, tCnstrs, tMap) = cnstrExpr(then, context)
          val (eType, eCnstrs, eMap) = cnstrExpr(elze, context)
          val newCnstrs = Equals(UnionType(Seq(tType, eType)), exprVarType) +: (tCnstrs ++ eCnstrs)
          (newCnstrs, (tMap ++ eMap)) 
        }
        case MatchExpr(scrut, cases) => {
          val (sType, sCnstrs, sMap) = cnstrExpr(scrut, context)
          val (pts, ptexpcnstr) = cases.map(mc => {
            val (pt, cnstrs, pvc) = pattern2Type(mc.pattern)
            val (expT, expC, expM) = cnstrExpr(mc.rhs, context ++ pvc)
            (pt, (expT, expC ++ cnstrs, expM))
          }).unzip
          val (cTypes, cCnstrs, cMaps) = unzip3(ptexpcnstr)
          val mCnstrs = cTypes.map(t => Include(t, exprVarType))
          val scrutPatternCnstr = Include(sType, UnionType(pts))
          val fMap: Map[Expr, VariableType] = cMaps.foldLeft(sMap)((a, m) => a ++ m)
          val finalCnstrs = scrutPatternCnstr +: (mCnstrs ++ cCnstrs.flatMap(x => x) ++ sCnstrs)
          (finalCnstrs, fMap)
        }
        case FunctionInvocation(fd, args) => {
          val (tArgs,rt) = funVars(fd)
          /*
          tArgs.zip(args).foreach{case (v, expr) => {
              val (newT, newCnstr) = cnstrExpr(expr, context)
              funCallsCnstr ++= newCnstr
              funCallsCnstr += Include(newT, v)
            }
          }
          */
          (Seq(Equals(rt, exprVarType)), Map[Expr, VariableType]())
        }
        case CaseClass(ccd, args) => {
          val (argsType, cnstrts, maps) = unzip3(args.map(e => cnstrExpr(e, context)))
          val fMap = maps.foldLeft(Map[Expr, VariableType]())((a, m) => a ++ m)
          val fcnstrts = Equals(ConstructorType(ccd.id.name, argsType), exprVarType) +: cnstrts.flatMap(x => x)
          (fcnstrts, fMap)
        }
        case _ => error("Not yet supported: " + expr)
      }
      (exprVarType, rels, (e2t: Map[Expr, VariableType]) + (expr -> exprVarType))
    }

    def pattern2Type(pattern: Pattern): (VariableType, Seq[Relation], Map[Identifier, VariableType]) = pattern match {
      case InstanceOfPattern(binder, ctd) => error("not yet supported")
      case WildcardPattern(binder) => {
        val v = freshVar(binder match {case Some(id) => id.name case None => "x"})
        (v, Seq[Relation](), binder match {case Some(id) => Map(id -> v) case None => Map()})
      }
      case CaseClassPattern(binder, ccd, sps) => {
        val cvt = freshVar(ccd.id.name)
        val (subConsType, cnstrs, subVarType) = unzip3(sps.map(p => pattern2Type(p)))
        val newMap = subVarType.foldLeft(Map[Identifier, VariableType]())((acc, el) => acc ++ el)
        val nCnstrs: Seq[Relation] = subConsType.zip(ccd.fields).zip(sps).foldLeft(cnstrs.flatMap(x => x))((a, el) => el match {
          case ((t, vd), sp) => sp match {
            case WildcardPattern(_) => a :+ Equals(t, cl2adt(vd.tpe.asInstanceOf[ClassType].classDef))
            case _ => a
          }
        })
        val ccnstr = Equals(ConstructorType(ccd.id.name, subConsType), cvt)
        (cvt, ccnstr +: nCnstrs, newMap)
      }
    }

    def cnstrFun(fd: FunDef): (Seq[Relation], Map[Expr, VariableType]) = {
      val argsT = funVars(fd)._1
      val argsID = fd.args.map(vd => vd.id)
      val context = argsID.zip(argsT).foldLeft(Map[Identifier, VariableType]())((acc, el) => acc + el)
      val (bodyType, cnstrts, map) = cnstrExpr(fd.body.get, context)
      (cnstrts :+ Include(bodyType, funVars(fd)._2), map)
    }

    def cnstrTypeHierarchy(pgm: Program): Seq[Relation] = {
      val caseClasses = pgm.definedClasses.filter(_.isInstanceOf[CaseClassDef])
      caseClasses.map(cc => Include(cl2adt(cc), cl2adt(cc.parent.get)))
    }

    def propagateEq(cnstrts: Set[Relation]): Set[Relation] = {
      null
    }

    val cnstrtsTypes = cnstrTypeHierarchy(pgm)

    val funs = pgm.definedFunctions
    val (cnstrtsFunctions, map) = funs.foldLeft(Seq[Relation](), Map[Expr, VariableType]())((a, f) => {
      val (rels, m) = cnstrFun(f)
      (a._1 ++ rels, a._2 ++ m)
    })
    (cnstrtsTypes ++ cnstrtsFunctions).toSet
  }

}
