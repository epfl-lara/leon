package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

trait CodeExtraction extends Extractors {
  self: AnalysisComponent =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._

  private lazy val setTraitSym = definitions.getClass("scala.collection.immutable.Set")

  private val varSubsts: scala.collection.mutable.Map[Symbol,Function0[Expr]] =
    scala.collection.mutable.Map.empty[Symbol,Function0[Expr]]
  private val classesToClasses: scala.collection.mutable.Map[Symbol,ClassTypeDef] =
    scala.collection.mutable.Map.empty[Symbol,ClassTypeDef]
  private val defsToDefs: scala.collection.mutable.Map[Symbol,FunDef] =
    scala.collection.mutable.Map.empty[Symbol,FunDef]

  def extractCode(unit: CompilationUnit): Program = { 
    import scala.collection.mutable.HashMap

    def s2ps(tree: Tree): Expr = toPureScala(unit)(tree) match {
      case Some(ex) => ex
      case None => stopIfErrors; scala.Predef.error("unreachable error.")
    }

    def st2ps(tree: Type): purescala.TypeTrees.TypeTree = toPureScalaType(unit)(tree) match {
      case Some(tt) => tt
      case None => stopIfErrors; scala.Predef.error("unreachable error.")
    }

    def extractTopLevelDef: ObjectDef = {
      val top = unit.body match {
        case p @ PackageDef(name, lst) if lst.size == 0 => {
          unit.error(p.pos, "No top-level definition found.")
          None
        }

        case PackageDef(name, lst) if lst.size > 1 => {
          unit.error(lst(1).pos, "Too many top-level definitions.")
          None
        }

        case PackageDef(name, lst) => {
          assert(lst.size == 1)
          lst(0) match {
            case ExObjectDef(n, templ) => Some(extractObjectDef(n.toString, templ))
            case other @ _ => unit.error(other.pos, "Expected: top-level single object.")
            None
          }
        }
      }

      stopIfErrors
      top.get
    }

    def extractObjectDef(nameStr: String, tmpl: Template): ObjectDef = {
      // we assume that the template actually corresponds to an object
      // definition. Typically it should have been obtained from the proper
      // extractor (ExObjectDef)

      var classDefs: List[ClassTypeDef] = Nil
      var objectDefs: List[ObjectDef] = Nil
      var funDefs: List[FunDef] = Nil

      val scalaClassSyms: scala.collection.mutable.Map[Symbol,Identifier] =
        scala.collection.mutable.Map.empty[Symbol,Identifier]
      val scalaClassArgs: scala.collection.mutable.Map[Symbol,Seq[(String,Tree)]] =
        scala.collection.mutable.Map.empty[Symbol,Seq[(String,Tree)]]
      val scalaClassNames: scala.collection.mutable.Set[String] = 
        scala.collection.mutable.Set.empty[String]

      // we need the new type definitions before we can do anything...
      tmpl.body.foreach(t =>
        t match {
          case ExAbstractClass(o2, sym) => {
            if(scalaClassNames.contains(o2)) {
              unit.error(t.pos, "A class with the same name already exists.")
            } else {
              scalaClassSyms += (sym -> FreshIdentifier(o2))
              scalaClassNames += o2
            }
          }
          case ExCaseClass(o2, sym, args) => {
            if(scalaClassNames.contains(o2)) {
              unit.error(t.pos, "A class with the same name already exists.")
            } else {
              scalaClassSyms  += (sym -> FreshIdentifier(o2))
              scalaClassNames += o2
              scalaClassArgs  += (sym -> args)
            }
          }
          case _ => ;
        }
      )

      stopIfErrors


      scalaClassSyms.foreach(p => {
          if(p._1.isAbstractClass) {
            classesToClasses += (p._1 -> new AbstractClassDef(p._2, None))
          } else if(p._1.isCase) {
            classesToClasses += (p._1 -> new CaseClassDef(p._2, None))
          }
      })

      classesToClasses.foreach(p => {
        val superC: List[ClassTypeDef] = p._1.tpe.baseClasses.filter(bcs => scalaClassSyms.exists(pp => pp._1 == bcs) && bcs != p._1).map(s => classesToClasses(s)).toList

        val superAC: List[AbstractClassDef] = superC.map(c => {
            if(!c.isInstanceOf[AbstractClassDef]) {
                unit.error(p._1.pos, "Class is inheriting from non-abstract class.")
                null
            } else {
                c.asInstanceOf[AbstractClassDef]
            }
        }).filter(_ != null)

        if(superAC.length > 1) {
            unit.error(p._1.pos, "Multiple inheritance.")
        }

        if(superAC.length == 1) {
            p._2.parent = Some(superAC.head)
        }

        if(p._2.isInstanceOf[CaseClassDef]) {
          // this should never fail
          val ccargs = scalaClassArgs(p._1)
          p._2.asInstanceOf[CaseClassDef].fields = ccargs.map(cca => {
            val cctpe = st2ps(cca._2.tpe)
            VarDecl(FreshIdentifier(cca._1).setType(cctpe), cctpe)
          })
        }
      })

      classDefs = classesToClasses.valuesIterator.toList
      
      // end of class (type) extraction

      // we now extract the function signatures.
      tmpl.body.foreach(
        _ match {
          case ExMainFunctionDef() => ;
          case dd @ ExFunctionDef(n,p,t,b) => {
            defsToDefs += (dd.symbol -> extractFunSig(n, p, t))
          }
          case _ => ;
        }
      )

      // then their bodies.
      tmpl.body.foreach(
        _ match {
          case ExMainFunctionDef() => ;
          case dd @ ExFunctionDef(n,p,t,b) => {
            val fd = defsToDefs(dd.symbol)
            defsToDefs(dd.symbol) = extractFunDef(fd, b)
          }
          case _ => ;
        }
      )

      funDefs = defsToDefs.valuesIterator.toList

      // we check nothing else is polluting the object.
      tmpl.body.foreach(
        _ match {
          case ExCaseClassSyntheticJunk() => ;
          // case ExObjectDef(o2, t2) => { objectDefs = extractObjectDef(o2, t2) :: objectDefs }
          case ExAbstractClass(_,_) => ; 
          case ExCaseClass(_,_,_) => ; 
          case ExConstructorDef() => ;
          case ExMainFunctionDef() => ;
          case ExFunctionDef(_,_,_,_) => ;
          case tree => { unit.error(tree.pos, "Don't know what to do with this. Not purescala?"); println(tree) }
        }
      )

      val name: Identifier = FreshIdentifier(nameStr)
      val theDef = new ObjectDef(name, objectDefs.reverse ::: classDefs ::: funDefs, Nil)
      
      theDef
    }

    def extractFunSig(nameStr: String, params: Seq[ValDef], tpt: Tree): FunDef = {
      val newParams = params.map(p => {
        val ptpe = st2ps(p.tpt.tpe)
        val newID = FreshIdentifier(p.name.toString).setType(ptpe)
        varSubsts(p.symbol) = (() => Variable(newID))
        VarDecl(newID, ptpe)
      })
      new FunDef(FreshIdentifier(nameStr), st2ps(tpt.tpe), newParams)
    }

    def extractFunDef(funDef: FunDef, body: Tree): FunDef = {
      var realBody = body
      var reqCont: Option[Expr] = None
      var ensCont: Option[Expr] = None

      realBody match {
        case ExEnsuredExpression(body2, resSym, contract) => {
          varSubsts(resSym) = (() => ResultVariable())
          val c1 = s2ps(contract)
          // varSubsts.remove(resSym)
          realBody = body2
          ensCont = Some(c1)
        }
        case _ => ;
      }

      realBody match {
        case ExRequiredExpression(body3, contract) => {
          realBody = body3
          reqCont = Some(s2ps(contract))
        }
        case _ => ;
      }
      
      val bodyAttempt = try {
        Some(scala2PureScala(unit, pluginInstance.silentlyTolerateNonPureBodies)(realBody))
      } catch {
        case e: ImpureCodeEncounteredException => None
      }

      funDef.body = bodyAttempt
      funDef.precondition = reqCont
      funDef.postcondition = ensCont
      funDef
    }

    // THE EXTRACTION CODE STARTS HERE
    val topLevelObjDef: ObjectDef = extractTopLevelDef

    stopIfErrors

    val programName: Identifier = unit.body match {
      case PackageDef(name, _) => FreshIdentifier(name.toString)
      case _ => FreshIdentifier("<program>")
    }

    //Program(programName, ObjectDef("Object", Nil, Nil))
    Program(programName, topLevelObjDef)
  }

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class ImpureCodeEncounteredException(tree: Tree) extends Exception

  /** Attempts to convert a scalac AST to a pure scala AST. */
  def toPureScala(unit: CompilationUnit)(tree: Tree): Option[Expr] = {
    try {
      Some(scala2PureScala(unit, false)(tree))
    } catch {
      case ImpureCodeEncounteredException(_) => None
    }
  }

  def toPureScalaType(unit: CompilationUnit)(typeTree: Type): Option[purescala.TypeTrees.TypeTree] = {
    try {
      Some(scalaType2PureScala(unit, false)(typeTree))
    } catch {
      case ImpureCodeEncounteredException(_) => None
    }
  }

  /** Forces conversion from scalac AST to purescala AST, throws an Exception
   * if impossible. If not in 'silent mode', non-pure AST nodes are reported as
   * errors. */
  private def scala2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Tree): Expr = {
    def rewriteCaseDef(cd: CaseDef): MatchCase = {
      def pat2pat(p: Tree): Pattern = p match {
        case Ident(nme.WILDCARD) => WildcardPattern(None)
        case b @ Bind(name, Ident(nme.WILDCARD)) => {
          val newID = FreshIdentifier(name.toString).setType(scalaType2PureScala(unit,silent)(b.symbol.tpe))
          varSubsts(b.symbol) = (() => Variable(newID))
          WildcardPattern(Some(newID))
        }
        case a @ Apply(fn, args) if fn.isType && a.tpe.typeSymbol.isCase && classesToClasses.keySet.contains(a.tpe.typeSymbol) => {
          val cd = classesToClasses(a.tpe.typeSymbol).asInstanceOf[CaseClassDef]
          assert(args.size == cd.fields.size)
          CaseClassPattern(None, cd, args.map(pat2pat(_)))
        }
        case b @ Bind(name, a @ Apply(fn, args)) if fn.isType && a.tpe.typeSymbol.isCase && classesToClasses.keySet.contains(a.tpe.typeSymbol) => {
          val newID = FreshIdentifier(name.toString).setType(scalaType2PureScala(unit,silent)(b.symbol.tpe))
          varSubsts(b.symbol) = (() => Variable(newID))
          val cd = classesToClasses(a.tpe.typeSymbol).asInstanceOf[CaseClassDef]
          assert(args.size == cd.fields.size)
          CaseClassPattern(Some(newID), cd, args.map(pat2pat(_)))
        }
        case _ => {
          if(!silent)
            unit.error(p.pos, "Unsupported pattern.")
          throw ImpureCodeEncounteredException(p)
        }
      }

      if(cd.guard == EmptyTree) {
        SimpleCase(pat2pat(cd.pat), rec(cd.body))
      } else {
        GuardedCase(pat2pat(cd.pat), rec(cd.guard), rec(cd.body))
      }
    }

    def rec(tr: Tree): Expr = tr match {
      case ExInt32Literal(v) => IntLiteral(v).setType(Int32Type)
      case ExBooleanLiteral(v) => BooleanLiteral(v).setType(BooleanType)
      case ExIdentifier(sym,tpt) => varSubsts.get(sym) match {
        case Some(fun) => fun()
        case None => {
          unit.error(tr.pos, "Unidentified variable.")
          throw ImpureCodeEncounteredException(tr)
        }
      }
      case ExCaseClassConstruction(tpt, args) => {
        val cctype = scalaType2PureScala(unit, silent)(tpt.tpe)
        if(!cctype.isInstanceOf[CaseClassType]) {
          if(!silent) {
            unit.error(tr.pos, "Construction of a non-case class.")
          }
          throw ImpureCodeEncounteredException(tree)
        }
        val nargs = args.map(rec(_))
        val cct = cctype.asInstanceOf[CaseClassType]
        CaseClass(cct.classDef, nargs).setType(cct)
      }
      case ExAnd(l, r) => And(rec(l), rec(r)).setType(BooleanType)
      case ExOr(l, r) => Or(rec(l), rec(r)).setType(BooleanType)
      case ExNot(e) => Not(rec(e)).setType(BooleanType)
      case ExUMinus(e) => UMinus(rec(e)).setType(Int32Type)
      case ExPlus(l, r) => Plus(rec(l), rec(r)).setType(Int32Type)
      case ExMinus(l, r) => Minus(rec(l), rec(r)).setType(Int32Type)
      case ExTimes(l, r) => Times(rec(l), rec(r)).setType(Int32Type)
      case ExDiv(l, r) => Division(rec(l), rec(r)).setType(Int32Type)
      case ExEquals(l, r) => Equals(rec(l), rec(r)).setType(BooleanType)
      case ExNotEquals(l, r) => Not(Equals(rec(l), rec(r)).setType(BooleanType)).setType(BooleanType)
      case ExGreaterThan(l, r) => GreaterThan(rec(l), rec(r)).setType(BooleanType)
      case ExGreaterEqThan(l, r) => GreaterEquals(rec(l), rec(r)).setType(BooleanType)
      case ExLessThan(l, r) => LessThan(rec(l), rec(r)).setType(BooleanType)
      case ExLessEqThan(l, r) => LessEquals(rec(l), rec(r)).setType(BooleanType)
      case ExFiniteSet(tt, args) => {
        val underlying = scalaType2PureScala(unit, silent)(tt.tpe)
          FiniteSet(args.map(rec(_))).setType(SetType(underlying))
      }
      case ExEmptySet(tt) => {
        val underlying = scalaType2PureScala(unit, silent)(tt.tpe)
        EmptySet(underlying).setType(SetType(underlying))          
      }
      case ExUnion(t1,t2) => {
        val rl = rec(t1)
        val rr = rec(t2)
        SetUnion(rl, rr).setType(rl.getType) // this is not entirely correct: should be a setype of LUB of underlying types of left and right.
      }
      case ExIntersection(t1,t2) => {
        val rl = rec(t1)
        val rr = rec(t2)
        SetIntersection(rl, rr).setType(rl.getType) // same as union
      } 
      case ExSetMinus(t1,t2) => {
        val rl = rec(t1)
        val rr = rec(t2)
        SetDifference(rl, rr).setType(rl.getType) // same as union
      } 
      case ExIfThenElse(t1,t2,t3) => {
        val r1 = rec(t1)
        val r2 = rec(t2)
        val r3 = rec(t3)
        IfExpr(r1, r2, r3).setType(leastUpperBound(r2.getType, r3.getType))
      }
      case ExLocalCall(sy,nm,ar) => {
        if(defsToDefs.keysIterator.find(_ == sy).isEmpty) {
          if(!silent)
            unit.error(tr.pos, "Invoking an invalid function.")
          throw ImpureCodeEncounteredException(tr)
        }
        val fd = defsToDefs(sy)
        FunctionInvocation(fd, ar.map(rec(_))).setType(fd.returnType)
      }
      case ExPatternMatching(sel, cses) => {
        val rs = rec(sel)
        val rc = cses.map(rewriteCaseDef(_))
        val rt: purescala.TypeTrees.TypeTree = rc.map(_.rhs.getType).reduceLeft(leastUpperBound(_,_))
        MatchExpr(rs, rc).setType(rt)
      }

      // this one should stay after all others, cause it also catches UMinus
      // and Not, for instance.
      case ExParameterlessMethodCall(t,n) => {
        val selector = rec(t)
        val selType = selector.getType

        if(!selType.isInstanceOf[CaseClassType]) {
          if(!silent)
            unit.error(tr.pos, "Invalid method or field invocation (not purescala?)")
          throw ImpureCodeEncounteredException(tr)
        }

        val selDef: CaseClassDef = selType.asInstanceOf[CaseClassType].classDef

        val fieldID = selDef.fields.find(_.id.name == n.toString) match {
          case None => {
            if(!silent)
              unit.error(tr.pos, "Invalid method or field invocation (not a case class arg?)")
            throw ImpureCodeEncounteredException(tr)
          }
          case Some(vd) => vd.id
        }

        CaseClassSelector(selector, fieldID).setType(fieldID.getType)
      }
  
      // default behaviour is to complain :)
      case _ => {
        if(!silent) {
          println(tr)
          reporter.info(tr.pos, "Could not extract as PureScala.", true)
        }
        throw ImpureCodeEncounteredException(tree)
      }
    }
    rec(tree)
  }

  private def scalaType2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Type): purescala.TypeTrees.TypeTree = {

    def rec(tr: Type): purescala.TypeTrees.TypeTree = tr match {
      case tpe if tpe == IntClass.tpe => Int32Type
      case tpe if tpe == BooleanClass.tpe => BooleanType
      case TypeRef(_, sym, btt :: Nil) if sym == setTraitSym => SetType(rec(btt))
      case TypeRef(_, sym, Nil) if classesToClasses.keySet.contains(sym) => classDefToClassType(classesToClasses(sym))

      case _ => {
        if(!silent) {
          unit.error(NoPosition, "Could not extract type as PureScala. [" + tr + "]")
        }
        throw ImpureCodeEncounteredException(null)
      }
      // case tt => {
      //   if(!silent) {
      //     unit.error(tree.pos, "This does not appear to be a type tree: [" + tt + "]")
      //   }
      //   throw ImpureCodeEncounteredException(tree)
      // }
    }

    rec(tree)
  }
}
