package setconstraints

import purescala.Definitions._
import purescala.Trees.{And => _, Equals => _, _}
import purescala.Common.Identifier
import purescala.TypeTrees.ClassType

import Trees._
import Tools._
import Manip._

object ConstraintsGenerator {

  def apply(pgm: Program): (Set[Relation], Set[VariableType], Map[String, Int]) = {
    val (traits, constructors) = adtExtractors(pgm)
    val funVars = labelFunction(pgm)

    val cnstrtsTypes = constraintsTypes(pgm.definedClasses, constructors, traits)
    val (cnstrtsFuns, exprMap) = constraintsFuns(pgm.definedFunctions, funVars, traits, constructors)

    val rels = cnstrtsTypes ++ cnstrtsFuns
    val frels = propagateEq(rels, traits.values.toSet ++ funVars.values.unzip._2.toSet)

    (frels, traits.map{
      case (_, v) => v
    }.toSet, constructors.map{
      case (_, ConstructorType(n, sts)) => (n, sts.size)
    })
  }

  def constraintsExpr(expr: Expr, 
                      context: Map[Identifier, VariableType], 
                      funVars: Map[FunDef, (Seq[VariableType], VariableType)],
                      traits: Map[AbstractClassDef, VariableType],
                      constructors: Map[CaseClassDef, ConstructorType]): (VariableType, Set[Relation], Map[Expr, VariableType]) = {

    val cl2adt: Map[ClassTypeDef, SetType] = traits.asInstanceOf[Map[ClassTypeDef, SetType]] ++ constructors.asInstanceOf[Map[ClassTypeDef, SetType]]

    def pattern2Type(pattern: Pattern): (VariableType, Set[Relation], Map[Identifier, VariableType]) = pattern match {
      case InstanceOfPattern(binder, ctd) => error("not yet supported")
      case WildcardPattern(binder) => {
        val v = freshVar(binder match {case Some(id) => id.name case None => "x"})
        (v, Set[Relation](), binder match {case Some(id) => Map(id -> v) case None => Map()})
      }
      case CaseClassPattern(binder, ccd, sps) => {
        val cvt = freshVar(ccd.id.name)
        val (subConsType, cnstrs, subVarType) = unzip3(sps.map(p => pattern2Type(p)))
        val newMap = subVarType.foldLeft(Map[Identifier, VariableType]())((acc, el) => acc ++ el)
        val nCnstrs: Set[Relation] = subConsType.zip(ccd.fields).zip(sps).foldLeft(cnstrs.toSet.flatten)((a, el) => el match {
          case ((t, vd), sp) => {
            val cd = vd.tpe.asInstanceOf[ClassType].classDef
            val cdt = cl2adt(cd)
            sp match {
              case WildcardPattern(_) => a + Equals(t, cdt)
              case _ => a
            }
          }
        })
        val ccnstr = Equals(ConstructorType(ccd.id.name, subConsType), cvt)
        (cvt, nCnstrs + ccnstr, newMap)
      }
    }

    def constraintsExpr0(expr: Expr, context: Map[Identifier, VariableType]): (VariableType, Set[Relation], Map[Expr, VariableType]) = {
      val exprVarType = freshVar("expr")
      val (rels, e2t) = expr match {
        case Variable(id) => {
          (Set[Relation](Equals(context(id), exprVarType)), Map[Expr, VariableType]())
        }
        case IfExpr(cond, then, elze) => {
          val (tType, tCnstrs, tMap) = constraintsExpr0(then, context)
          val (eType, eCnstrs, eMap) = constraintsExpr0(elze, context)
          val newCnstrs = (tCnstrs ++ eCnstrs) + Equals(UnionType(Seq(tType, eType)), exprVarType)
          (newCnstrs, (tMap ++ eMap))
        }
        case MatchExpr(scrut, cases) => {
          val (sType, sCnstrs, sMap) = constraintsExpr0(scrut, context)
          val (pts, ptexpcnstr) = cases.map(mc => {
            val (pt, cnstrs, pvc) = pattern2Type(mc.pattern)
            val (expT, expC, expM) = constraintsExpr0(mc.rhs, context ++ pvc)
            (pt, (expT, expC ++ cnstrs, expM))
          }).unzip
          val (cTypes, cCnstrs, cMaps) = unzip3(ptexpcnstr)
          val mCnstrs: Set[Relation] = cTypes.toSet.map((t: VariableType) => Include(t, exprVarType))
          val scrutPatternCnstr: Relation = Include(sType, UnionType(pts))
          val fMap: Map[Expr, VariableType] = cMaps.foldLeft(sMap)((a, m) => a ++ m)
          val finalCnstrs = (mCnstrs ++ cCnstrs.flatten ++ sCnstrs) + scrutPatternCnstr 
          (finalCnstrs, fMap)
        }
        case FunctionInvocation(fd, args) => {
          val (tArgs,rt) = funVars(fd)
          (Set[Relation](Equals(rt, exprVarType)), Map[Expr, VariableType]())
        }
        case CaseClass(ccd, args) => {
          val (argsType, cnstrts, maps) = unzip3(args.map(e => constraintsExpr0(e, context)))
          val fMap = maps.foldLeft(Map[Expr, VariableType]())((a, m) => a ++ m)
          val fcnstrts = cnstrts.toSet. flatten + Equals(ConstructorType(ccd.id.name, argsType), exprVarType)
          (fcnstrts, fMap)
        }
        case _ => error("Not yet supported: " + expr)
      }
      (exprVarType, rels, (e2t: Map[Expr, VariableType]) + (expr -> exprVarType))
    }

    constraintsExpr0(expr, context)
  }

  def propagateEq(cnstrts: Set[Relation], keywords: Set[VariableType]): Set[Relation] = {
    def iter(cnstrts: Set[Relation]): Set[Relation] = {
      /*
      cnstrts.foldLeft(cnstrts)((a, rel) => rel match {
        case Equals(v1@VariableType(_), v2@VariableType(_)) if traits.contains(v1) =>
          (a - rel).map(substitute(_, v2, v1))
        case Equals(v1@VariableType(_), v2@VariableType(_)) if traits.contains(v2) =>
          (a - rel).map(substitute(_, v1, v2))
        case _ => a
      }
      val (eq, rest) = extract((rel: Relation) => rel match {
        case Equals(v1@VariableType(_), v2@VariableType(_)) if traits.contains(v1) || traits.contains(v2) => true
        case _ => false
      }, cnstrts)
      eq match {
        case None => cnstrts
        case Some(Equals(v1@VariableType(_), v2@VariableType(_))) if traits.contains(v1) => rest.map(substitute(_, v2, v1))
        case Some(Equals(v1@VariableType(_), v2@VariableType(_))) if traits.contains(v2) => rest.map(substitute(_, v1, v2))
        case _ => error("no way...")
      }
      */
      val (eq, rest) = extract((rel: Relation) => rel match {
        case Equals(v@VariableType(_), s) if !keywords.contains(v) => true
        case Equals(s, v@VariableType(_)) if !keywords.contains(v) => true
        case _ => false
      }, cnstrts)
      eq match {
        case None => cnstrts
        case Some(Equals(v@VariableType(_), s)) if !keywords.contains(v) => rest.map(substitute(_, v, s))
        case Some(Equals(s, v@VariableType(_))) if !keywords.contains(v) => rest.map(substitute(_, v, s))
        case _ => error("no way...")
      }
    }
    fix(iter, cnstrts)
  }


  def constraintsFuns(fds: Seq[FunDef],
                      funVars: Map[FunDef, (Seq[VariableType], VariableType)],
                      traits: Map[AbstractClassDef, VariableType],
                      constructors: Map[CaseClassDef, ConstructorType]): (Set[Relation], Map[Expr, VariableType]) =
    fds.foldLeft(Set[Relation](), Map[Expr, VariableType]())((a, f) => {
      val (rels, m) = constraintsFun(f, funVars, traits, constructors)
      (a._1 ++ rels, a._2 ++ m)
    })

  def constraintsFun(fd: FunDef, 
                     funVars: Map[FunDef, (Seq[VariableType], VariableType)],
                     traits: Map[AbstractClassDef, VariableType],
                     constructors: Map[CaseClassDef, ConstructorType]): (Set[Relation], Map[Expr, VariableType]) = {
    val argsT = funVars(fd)._1
    val argsID = fd.args.map(vd => vd.id)
    val context = argsID.zip(argsT).foldLeft(Map[Identifier, VariableType]())((acc, el) => acc + el)
    val (bodyType, cnstrts, map) = constraintsExpr(fd.body.get, context, funVars, traits, constructors)
    (cnstrts + Include(bodyType, funVars(fd)._2), map)
  }

  def constraintsTypes(cls: Seq[ClassTypeDef], constructors: Map[CaseClassDef, ConstructorType], traits: Map[AbstractClassDef, VariableType]): Set[Relation] = {
    val caseClasses: Seq[CaseClassDef] = cls.filter(_.isInstanceOf[CaseClassDef]).asInstanceOf[Seq[CaseClassDef]]
    caseClasses.map(cc => {
      val parent: AbstractClassDef = cc.parent.get
      Include(constructors(cc), traits(parent))
    }).toSet
  }

  def labelFunction(pgm: Program): Map[FunDef, (Seq[VariableType], VariableType)] =
    pgm.definedFunctions.foldLeft(Map[FunDef, (Seq[VariableType], VariableType)]())((a, fd) => {
      val varTypes = (fd.args.map(vd => freshVar(fd.id.name + "_arg_" + vd.id.name)), freshVar(fd.id.name + "_return"))
      a + (fd -> varTypes)
    })

  def adtExtractors(pgm: Program): (Map[AbstractClassDef, VariableType], Map[CaseClassDef, ConstructorType]) = {
    import scala.collection.mutable.HashMap
    val traits = new HashMap[AbstractClassDef, VariableType]
    val constructors = new HashMap[CaseClassDef, ConstructorType]
    var dcls = pgm.definedClasses
    while(!dcls.isEmpty) {
      val curr = dcls.head
      if(curr.isInstanceOf[AbstractClassDef]) {
        val trai = curr.asInstanceOf[AbstractClassDef]
        traits.put(trai, freshVar(curr.id.name))
        dcls = dcls.filterNot(_ == trai)
      } else if(curr.isInstanceOf[CaseClassDef]) {
        val cc = curr.asInstanceOf[CaseClassDef]
        val name = cc.id.name
        val fields = cc.fields
        try {
          val l = fields.map(vd => traits(vd.tpe.asInstanceOf[ClassType].classDef.asInstanceOf[AbstractClassDef])).toList //hack, fields might be case class too
          constructors.put(cc, ConstructorType(name, l))
          dcls = dcls.filterNot(_ == cc)
        } catch {
          case _: NoSuchElementException => {
            dcls = dcls.tail ++ List(dcls.head)
          }
        }
      } else error("Found a class which is neither an AbstractClassDef nor a CaseClassDef")
    }
    (Map(traits.toSeq: _*), Map(constructors.toSeq: _*))
  }

}
