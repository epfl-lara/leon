package leon
package plugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees.{Block => PBlock, _}
import purescala.TypeTrees._
import purescala.Common._

trait CodeExtraction extends Extractors {
  self: AnalysisComponent =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._

  private lazy val setTraitSym = definitions.getClass("scala.collection.immutable.Set")
  private lazy val mapTraitSym = definitions.getClass("scala.collection.immutable.Map")
  private lazy val multisetTraitSym = try {
    definitions.getClass("scala.collection.immutable.Multiset")
  } catch {
    case _ => null
  }
  private lazy val optionClassSym     = definitions.getClass("scala.Option")
  private lazy val someClassSym       = definitions.getClass("scala.Some")
  private lazy val function1TraitSym  = definitions.getClass("scala.Function1")

  private lazy val arraySym           = definitions.getClass("scala.Array")

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def isTuple2(sym : Symbol) : Boolean = sym == tuple2Sym
  def isTuple3(sym : Symbol) : Boolean = sym == tuple3Sym
  def isTuple4(sym : Symbol) : Boolean = sym == tuple4Sym
  def isTuple5(sym : Symbol) : Boolean = sym == tuple5Sym

  def isSetTraitSym(sym : Symbol) : Boolean = {
    sym == setTraitSym || sym.tpe.toString.startsWith("scala.Predef.Set")
  }

  def isMapTraitSym(sym : Symbol) : Boolean = {
    sym == mapTraitSym || sym.tpe.toString.startsWith("scala.Predef.Map")
  }

  def isMultisetTraitSym(sym : Symbol) : Boolean = {
    sym == multisetTraitSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction1TraitSym(sym : Symbol) : Boolean = {
    sym == function1TraitSym
  }

  private val mutableVarSubsts: scala.collection.mutable.Map[Symbol,Function0[Expr]] =
    scala.collection.mutable.Map.empty[Symbol,Function0[Expr]]
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
      case None => stopIfErrors; scala.sys.error("unreachable error.")
    }

    def st2ps(tree: Type): purescala.TypeTrees.TypeTree = toPureScalaType(unit)(tree) match {
      case Some(tt) => tt
      case None => stopIfErrors; scala.sys.error("unreachable error.")
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
            classesToClasses += (p._1 -> new AbstractClassDef(p._2))
          } else if(p._1.isCase) {
            classesToClasses += (p._1 -> new CaseClassDef(p._2))
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
            p._2.setParent(superAC.head)
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
            val mods = dd.mods
            val funDef = extractFunSig(n, p, t).setPosInfo(dd.pos.line, dd.pos.column)
            if(mods.isPrivate) funDef.addAnnotation("private")
            for(a <- dd.symbol.annotations) {
              a.atp.safeToString match {
                case "leon.Annotations.induct" => funDef.addAnnotation("induct")
                case "leon.Annotations.axiomatize" => funDef.addAnnotation("axiomatize")
                case _ => ;
              }
            }
            defsToDefs += (dd.symbol -> funDef)
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
          varSubsts(resSym) = (() => ResultVariable().setType(funDef.returnType))
          val c1 = s2ps(contract)
          // varSubsts.remove(resSym)
          realBody = body2
          ensCont = Some(c1)
        }
        case ExHoldsExpression(body2) => {
          realBody = body2
          ensCont = Some(ResultVariable().setType(BooleanType))
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
        Some(flattenBlocks(scala2PureScala(unit, pluginInstance.silentlyTolerateNonPureBodies)(realBody)))
      } catch {
        case e: ImpureCodeEncounteredException => None
      }

      reqCont.map(e => 
        if(containsLetDef(e)) {
          unit.error(realBody.pos, "Function precondtion should not contain nested function definition")
          throw ImpureCodeEncounteredException(realBody)
        })
      ensCont.map(e => 
        if(containsLetDef(e)) {
          unit.error(realBody.pos, "Function postcondition should not contain nested function definition")
          throw ImpureCodeEncounteredException(realBody)
        })
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


  private var currentFunDef: FunDef = null
  private var owners: Map[Expr, Option[FunDef]] = Map()

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
        case a@Apply(fn, args) => {
          val pst = scalaType2PureScala(unit, silent)(a.tpe)
          pst match {
            case TupleType(argsTpes) => TuplePattern(None, args.map(pat2pat))
            case _ => throw ImpureCodeEncounteredException(p)
          }
        }
        case b @ Bind(name, a @ Apply(fn, args)) => {
          val newID = FreshIdentifier(name.toString).setType(scalaType2PureScala(unit,silent)(b.symbol.tpe))
          varSubsts(b.symbol) = (() => Variable(newID))
          val pst = scalaType2PureScala(unit, silent)(a.tpe)
          pst match {
            case TupleType(argsTpes) => TuplePattern(Some(newID), args.map(pat2pat))
            case _ => throw ImpureCodeEncounteredException(p)
          }
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
        val recPattern = pat2pat(cd.pat)
        val recGuard = rec(cd.guard)
        val recBody = rec(cd.body)
        if(!isPure(recGuard)) {
          unit.error(cd.guard.pos, "Guard expression must be pure")
          throw ImpureCodeEncounteredException(cd)
        }
        GuardedCase(recPattern, recGuard, recBody)
      }
    }

    def extractFunSig(nameStr: String, params: Seq[ValDef], tpt: Tree): FunDef = {
      val newParams = params.map(p => {
        val ptpe =  scalaType2PureScala(unit, silent) (p.tpt.tpe)
        val newID = FreshIdentifier(p.name.toString).setType(ptpe)
        varSubsts(p.symbol) = (() => Variable(newID))
        VarDecl(newID, ptpe)
      })
      new FunDef(FreshIdentifier(nameStr), scalaType2PureScala(unit, silent)(tpt.tpe), newParams)
    }

    def extractFunDef(funDef: FunDef, body: Tree): FunDef = {
      var realBody = body
      var reqCont: Option[Expr] = None
      var ensCont: Option[Expr] = None
      
      currentFunDef = funDef

      realBody match {
        case ExEnsuredExpression(body2, resSym, contract) => {
          varSubsts(resSym) = (() => ResultVariable().setType(funDef.returnType))
          val c1 = scala2PureScala(unit, pluginInstance.silentlyTolerateNonPureBodies) (contract)
          // varSubsts.remove(resSym)
          realBody = body2
          ensCont = Some(c1)
        }
        case ExHoldsExpression(body2) => {
          realBody = body2
          ensCont = Some(ResultVariable().setType(BooleanType))
        }
        case _ => ;
      }

      realBody match {
        case ExRequiredExpression(body3, contract) => {
          realBody = body3
          reqCont = Some(scala2PureScala(unit, pluginInstance.silentlyTolerateNonPureBodies) (contract))
        }
        case _ => ;
      }
      
      val bodyAttempt = try {
        Some(flattenBlocks(scala2PureScala(unit, pluginInstance.silentlyTolerateNonPureBodies)(realBody)))
      } catch {
        case e: ImpureCodeEncounteredException => None
      }

      bodyAttempt.foreach(e => 
        if(e.getType.isInstanceOf[ArrayType] && owners.get(e).getOrElse(null) != funDef) {
          unit.error(realBody.pos, "Function cannot return an array that is not locally defined")
          throw ImpureCodeEncounteredException(realBody)
        })

      reqCont.foreach(e => 
        if(containsLetDef(e)) {
          unit.error(realBody.pos, "Function precondtion should not contain nested function definition")
          throw ImpureCodeEncounteredException(realBody)
        })
      ensCont.foreach(e => 
        if(containsLetDef(e)) {
          unit.error(realBody.pos, "Function postcondition should not contain nested function definition")
          throw ImpureCodeEncounteredException(realBody)
        })
      funDef.body = bodyAttempt
      funDef.precondition = reqCont
      funDef.postcondition = ensCont
      funDef
    }

    def rec(tr: Tree): Expr = {
      
      val (nextExpr, rest) = tr match {
        case Block(Block(e :: es1, l1) :: es2, l2) => (e, Some(Block(es1 ++ Seq(l1) ++ es2, l2)))
        case Block(e :: Nil, last) => (e, Some(last))
        case Block(e :: es, last) => (e, Some(Block(es, last)))
        case _ => (tr, None)
      }

      var handleRest = true
      val psExpr = nextExpr match {
        case ExTuple(tpes, exprs) => {
          val tupleType = TupleType(tpes.map(tpe => scalaType2PureScala(unit, silent)(tpe)))
          val tupleExprs = exprs.map(e => rec(e))
          Tuple(tupleExprs).setType(tupleType)
        }
        case ExTupleExtract(tuple, index) => {
          val tupleExpr = rec(tuple)
          val TupleType(tpes) = tupleExpr.getType
          if(tpes.size < index)
            throw ImpureCodeEncounteredException(tree)
          else
            TupleSelect(tupleExpr, index).setType(tpes(index-1))
        }
        case ExValDef(vs, tpt, bdy) => {
          val binderTpe = scalaType2PureScala(unit, silent)(tpt.tpe)
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = rec(bdy)
          val restTree = rest match {
            case Some(rst) => {
              varSubsts(vs) = (() => Variable(newID))
              val res = rec(rst)
              varSubsts.remove(vs)
              res
            }
            case None => UnitLiteral
          }
          handleRest = false
          val res = Let(newID, valTree, restTree)
          res
        }
        case dd@ExFunctionDef(n, p, t, b) => {
          val funDef = extractFunSig(n, p, t).setPosInfo(dd.pos.line, dd.pos.column)
          defsToDefs += (dd.symbol -> funDef)
          val oldMutableVarSubst = mutableVarSubsts.toMap //take an immutable snapshot of the map
          mutableVarSubsts.clear //reseting the visible mutable vars, we do not handle mutable variable closure in nested functions
          val funDefWithBody = extractFunDef(funDef, b)
          mutableVarSubsts ++= oldMutableVarSubst
          val restTree = rest match {
            case Some(rst) => rec(rst)
            case None => UnitLiteral
          }
          defsToDefs.remove(dd.symbol)
          handleRest = false
          LetDef(funDefWithBody, restTree)
        }
        case ExVarDef(vs, tpt, bdy) => {
          val binderTpe = scalaType2PureScala(unit, silent)(tpt.tpe)
          binderTpe match {
            case ArrayType(_) => 
              unit.error(tree.pos, "Cannot declare array variables, only val are alllowed")
              throw ImpureCodeEncounteredException(tree)
            case _ =>
          }
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = rec(bdy)
          mutableVarSubsts += (vs -> (() => Variable(newID)))
          val restTree = rest match {
            case Some(rst) => {
              varSubsts(vs) = (() => Variable(newID))
              val res = rec(rst)
              varSubsts.remove(vs)
              res
            }
            case None => UnitLiteral
          }
          handleRest = false
          val res = LetVar(newID, valTree, restTree)
          res
        }

        case ExAssign(sym, rhs) => mutableVarSubsts.get(sym) match {
          case Some(fun) => {
            val Variable(id) = fun()
            val rhsTree = rec(rhs)
            Assignment(id, rhsTree)
          }
          case None => {
            unit.error(tr.pos, "Undeclared variable.")
            throw ImpureCodeEncounteredException(tr)
          }
        }
        case wh@ExWhile(cond, body) => {
          val condTree = rec(cond)
          val bodyTree = rec(body)
          While(condTree, bodyTree).setPosInfo(wh.pos.line,wh.pos.column)
        }
        case wh@ExWhileWithInvariant(cond, body, inv) => {
          val condTree = rec(cond)
          val bodyTree = rec(body)
          val invTree = rec(inv)
          val w = While(condTree, bodyTree).setPosInfo(wh.pos.line,wh.pos.column)
          w.invariant = Some(invTree)
          w
        }

        case ExInt32Literal(v) => IntLiteral(v).setType(Int32Type)
        case ExBooleanLiteral(v) => BooleanLiteral(v).setType(BooleanType)
        case ExUnitLiteral() => UnitLiteral

        case ExTyped(e,tpt) => rec(e)
        case ExIdentifier(sym,tpt) => varSubsts.get(sym) match {
          case Some(fun) => fun()
          case None => mutableVarSubsts.get(sym) match {
            case Some(fun) => fun()
            case None => {
              unit.error(tr.pos, "Unidentified variable.")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }
        case epsi@ExEpsilonExpression(tpe, varSym, predBody) => {
          val pstpe = scalaType2PureScala(unit, silent)(tpe)
          val previousVarSubst: Option[Function0[Expr]] = varSubsts.get(varSym) //save the previous in case of nested epsilon
          varSubsts(varSym) = (() => EpsilonVariable((epsi.pos.line, epsi.pos.column)).setType(pstpe))
          val c1 = rec(predBody)
          previousVarSubst match {
            case Some(f) => varSubsts(varSym) = f
            case None => varSubsts.remove(varSym)
          }
          if(containsEpsilon(c1)) {
            unit.error(epsi.pos, "Usage of nested epsilon is not allowed.")
            throw ImpureCodeEncounteredException(epsi)
          }
          Epsilon(c1).setType(pstpe).setPosInfo(epsi.pos.line, epsi.pos.column)
        }
        case ExSomeConstruction(tpe, arg) => {
          // println("Got Some !" + tpe + ":" + arg)
          val underlying = scalaType2PureScala(unit, silent)(tpe)
          OptionSome(rec(arg)).setType(OptionType(underlying))
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
        case ExMod(l, r) => Modulo(rec(l), rec(r)).setType(Int32Type)
        case ExEquals(l, r) => {
          val rl = rec(l)
          val rr = rec(r)
          ((rl.getType,rr.getType) match {
            case (SetType(_), SetType(_)) => SetEquals(rl, rr)
            case (BooleanType, BooleanType) => Iff(rl, rr)
            case (_, _) => Equals(rl, rr)
          }).setType(BooleanType) 
        }
        case ExNotEquals(l, r) => Not(Equals(rec(l), rec(r)).setType(BooleanType)).setType(BooleanType)
        case ExGreaterThan(l, r) => GreaterThan(rec(l), rec(r)).setType(BooleanType)
        case ExGreaterEqThan(l, r) => GreaterEquals(rec(l), rec(r)).setType(BooleanType)
        case ExLessThan(l, r) => LessThan(rec(l), rec(r)).setType(BooleanType)
        case ExLessEqThan(l, r) => LessEquals(rec(l), rec(r)).setType(BooleanType)
        case ExFiniteSet(tt, args) => {
          val underlying = scalaType2PureScala(unit, silent)(tt.tpe)
          FiniteSet(args.map(rec(_))).setType(SetType(underlying))
        }
        case ExFiniteMultiset(tt, args) => {
          val underlying = scalaType2PureScala(unit, silent)(tt.tpe)
          FiniteMultiset(args.map(rec(_))).setType(MultisetType(underlying))
        }
        case ExEmptySet(tt) => {
          val underlying = scalaType2PureScala(unit, silent)(tt.tpe)
          EmptySet(underlying).setType(SetType(underlying))          
        }
        case ExEmptyMultiset(tt) => {
          val underlying = scalaType2PureScala(unit, silent)(tt.tpe)
          EmptyMultiset(underlying).setType(MultisetType(underlying))          
        }
        case ExEmptyMap(ft, tt) => {
          val fromUnderlying = scalaType2PureScala(unit, silent)(ft.tpe)
          val toUnderlying   = scalaType2PureScala(unit, silent)(tt.tpe)
          EmptyMap(fromUnderlying, toUnderlying).setType(MapType(fromUnderlying, toUnderlying))
        }
        case ExSetMin(t) => {
          val set = rec(t)
          if(!set.getType.isInstanceOf[SetType]) {
            if(!silent) unit.error(t.pos, "Min should be computed on a set.")
            throw ImpureCodeEncounteredException(tree)
          }
          SetMin(set).setType(set.getType.asInstanceOf[SetType].base)
        }
        case ExSetMax(t) => {
          val set = rec(t)
          if(!set.getType.isInstanceOf[SetType]) {
            if(!silent) unit.error(t.pos, "Max should be computed on a set.")
            throw ImpureCodeEncounteredException(tree)
          }
          SetMax(set).setType(set.getType.asInstanceOf[SetType].base)
        }
        case ExUnion(t1,t2) => {
          val rl = rec(t1)
          val rr = rec(t2)
          rl.getType match {
            case s @ SetType(_) => SetUnion(rl, rr).setType(s)
            case m @ MultisetType(_) => MultisetUnion(rl, rr).setType(m)
            case _ => {
              if(!silent) unit.error(tree.pos, "Union of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case ExIntersection(t1,t2) => {
          val rl = rec(t1)
          val rr = rec(t2)
          rl.getType match {
            case s @ SetType(_) => SetIntersection(rl, rr).setType(s)
            case m @ MultisetType(_) => MultisetIntersection(rl, rr).setType(m)
            case _ => {
              if(!silent) unit.error(tree.pos, "Intersection of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case ExSetContains(t1,t2) => {
          val rl = rec(t1)
          val rr = rec(t2)
          rl.getType match {
            case s @ SetType(_) => ElementOfSet(rr, rl)
            case _ => {
              if(!silent) unit.error(tree.pos, ".contains on non set expression.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case ExSetSubset(t1,t2) => {
          val rl = rec(t1)
          val rr = rec(t2)
          rl.getType match {
            case s @ SetType(_) => SubsetOf(rl, rr)
            case _ => {
              if(!silent) unit.error(tree.pos, "Subset on non set expression.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case ExSetMinus(t1,t2) => {
          val rl = rec(t1)
          val rr = rec(t2)
          rl.getType match {
            case s @ SetType(_) => SetDifference(rl, rr).setType(s)
            case m @ MultisetType(_) => MultisetDifference(rl, rr).setType(m)
            case _ => {
              if(!silent) unit.error(tree.pos, "Difference of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        } 
        case ExSetCard(t) => {
          val rt = rec(t)
          rt.getType match {
            case s @ SetType(_) => SetCardinality(rt)
            case m @ MultisetType(_) => MultisetCardinality(rt)
            case _ => {
              if(!silent) unit.error(tree.pos, "Cardinality of non set/multiset expressions.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case ExMultisetToSet(t) => {
          val rt = rec(t)
          rt.getType match {
            case m @ MultisetType(u) => MultisetToSet(rt).setType(SetType(u))
            case _ => {
              if(!silent) unit.error(tree.pos, "toSet can only be applied to multisets.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case up@ExUpdated(m,f,t) => {
          val rm = rec(m)
          val rf = rec(f)
          val rt = rec(t)
          rm.getType match {
            case MapType(ft, tt) => {
              val newSingleton = SingletonMap(rf, rt).setType(rm.getType)
              MapUnion(rm, FiniteMap(Seq(newSingleton)).setType(rm.getType)).setType(rm.getType)
            }
            case ArrayType(bt) => {
              ArrayUpdated(rm, rf, rt).setType(rm.getType).setPosInfo(up.pos.line, up.pos.column)
            }
            case _ => {
              if (!silent) unit.error(tree.pos, "updated can only be applied to maps.")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        case ExMapIsDefinedAt(m,k) => {
          val rm = rec(m)
          val rk = rec(k)
          MapIsDefinedAt(rm, rk)
        }

        case ExPlusPlusPlus(t1,t2) => {
          val rl = rec(t1)
          val rr = rec(t2)
          MultisetPlus(rl, rr).setType(rl.getType)
        }
        case app@ExApply(lhs,args) => {
          val rlhs = rec(lhs)
          val rargs = args map rec
          rlhs.getType match {
            case MapType(_,tt) => 
              assert(rargs.size == 1)
              MapGet(rlhs, rargs.head).setType(tt).setPosInfo(app.pos.line, app.pos.column)
            case FunctionType(fts, tt) => {
              rlhs match {
                case Variable(id) =>
                  AnonymousFunctionInvocation(id, rargs).setType(tt)
                case _ => {
                  if (!silent) unit.error(tree.pos, "apply on non-variable or non-map expression")
                  throw ImpureCodeEncounteredException(tree)
                }
              }
            }
            case ArrayType(bt) => {
              assert(rargs.size == 1)
              ArraySelect(rlhs, rargs.head).setType(bt).setPosInfo(app.pos.line, app.pos.column)
            }
            case _ => {
              if (!silent) unit.error(tree.pos, "apply on unexpected type")
              throw ImpureCodeEncounteredException(tree)
            }
          }
        }
        // for now update only occurs on Array. later we might have to distinguished depending on the type of the lhs
        case update@ExUpdate(lhs, index, newValue) => { 
          val lhsRec = rec(lhs)
          lhsRec match {
            case Variable(_) =>
            case _ => {
              unit.error(tree.pos, "array update only works on variables")
              throw ImpureCodeEncounteredException(tree)
            }
          }
          val indexRec = rec(index)
          val newValueRec = rec(newValue)
          ArrayUpdate(lhsRec, indexRec, newValueRec).setPosInfo(update.pos.line, update.pos.column)
        }
        case ExArrayLength(t) => {
          val rt = rec(t)
          ArrayLength(rt)
        }
        case ExArrayFill(baseType, length, defaultValue) => {
          val underlying = scalaType2PureScala(unit, silent)(baseType.tpe)
          val lengthRec = rec(length)
          val defaultValueRec = rec(defaultValue)
          ArrayFill(lengthRec, defaultValueRec).setType(ArrayType(underlying))
        }
        case ExIfThenElse(t1,t2,t3) => {
          val r1 = rec(t1)
          if(containsLetDef(r1)) {
            unit.error(t1.pos, "Condition of if-then-else expression should not contain nested function definition")
            throw ImpureCodeEncounteredException(t1)
          }
          val r2 = rec(t2)
          val r3 = rec(t3)
          val lub = leastUpperBound(r2.getType, r3.getType)
          lub match {
            case Some(lub) => IfExpr(r1, r2, r3).setType(lub)
            case None =>
              unit.error(nextExpr.pos, "Both branches of ifthenelse have incompatible types")
              throw ImpureCodeEncounteredException(t1)
          }
        }

        case ExIsInstanceOf(tt, cc) => {
          val ccRec = rec(cc)
          val checkType = scalaType2PureScala(unit, silent)(tt.tpe)
          checkType match {
            case CaseClassType(ccd) => {
              val rootType: ClassTypeDef  = if(ccd.parent != None) ccd.parent.get else ccd
              if(!ccRec.getType.isInstanceOf[ClassType]) {
                unit.error(tr.pos, "isInstanceOf can only be used with a case class")
                throw ImpureCodeEncounteredException(tr)
              } else {
                val testedExprType = ccRec.getType.asInstanceOf[ClassType].classDef
                val testedExprRootType: ClassTypeDef = if(testedExprType.parent != None) testedExprType.parent.get else testedExprType

                if(rootType != testedExprRootType) {
                  unit.error(tr.pos, "isInstanceOf can only be used with compatible case classes")
                  throw ImpureCodeEncounteredException(tr)
                } else {
                  CaseClassInstanceOf(ccd, ccRec) 
                }
              }
            }
            case _ => {
              unit.error(tr.pos, "isInstanceOf can only be used with a case class")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }

        case lc @ ExLocalCall(sy,nm,ar) => {
          if(defsToDefs.keysIterator.find(_ == sy).isEmpty) {
            if(!silent)
              unit.error(tr.pos, "Invoking an invalid function.")
            throw ImpureCodeEncounteredException(tr)
          }
          val fd = defsToDefs(sy)
          FunctionInvocation(fd, ar.map(rec(_))).setType(fd.returnType).setPosInfo(lc.pos.line,lc.pos.column) 
        }
        case pm @ ExPatternMatching(sel, cses) => {
          val rs = rec(sel)
          val rc = cses.map(rewriteCaseDef(_))
          val rt: purescala.TypeTrees.TypeTree = rc.map(_.rhs.getType).reduceLeft(leastUpperBound(_,_).get)
          MatchExpr(rs, rc).setType(rt).setPosInfo(pm.pos.line,pm.pos.column)
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

          CaseClassSelector(selDef, selector, fieldID).setType(fieldID.getType)
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

      if(handleRest) {
        rest match {
          case Some(rst) => {
            val recRst = rec(rst)
            PBlock(Seq(psExpr), recRst).setType(recRst.getType)
          }
          case None => psExpr
        }
      } else {
        psExpr
      }
    }
    rec(tree)
  }

  private def scalaType2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Type): purescala.TypeTrees.TypeTree = {

    def rec(tr: Type): purescala.TypeTrees.TypeTree = tr match {
      case tpe if tpe == IntClass.tpe => Int32Type
      case tpe if tpe == BooleanClass.tpe => BooleanType
      case tpe if tpe == UnitClass.tpe => UnitType
      case TypeRef(_, sym, btt :: Nil) if isSetTraitSym(sym) => SetType(rec(btt))
      case TypeRef(_, sym, btt :: Nil) if isMultisetTraitSym(sym) => MultisetType(rec(btt))
      case TypeRef(_, sym, btt :: Nil) if isOptionClassSym(sym) => OptionType(rec(btt))
      case TypeRef(_, sym, List(ftt,ttt)) if isMapTraitSym(sym) => MapType(rec(ftt),rec(ttt))
      case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) => TupleType(Seq(rec(t1),rec(t2)))
      case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) => TupleType(Seq(rec(t1),rec(t2),rec(t3)))
      case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) => TupleType(Seq(rec(t1),rec(t2),rec(t3),rec(t4)))
      case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) => TupleType(Seq(rec(t1),rec(t2),rec(t3),rec(t4),rec(t5)))
      case TypeRef(_, sym, ftt :: ttt :: Nil) if isFunction1TraitSym(sym) => FunctionType(List(rec(ftt)), rec(ttt))
      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) => ArrayType(rec(btt))
      case TypeRef(_, sym, Nil) if classesToClasses.keySet.contains(sym) => classDefToClassType(classesToClasses(sym))
      case _ => {
        if(!silent) {
          unit.error(NoPosition, "Could not extract type as PureScala. [" + tr + "]")
          throw new Exception("aouch")
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

  def mkPosString(pos: scala.tools.nsc.util.Position) : String = {
    pos.line + "," + pos.column
  }
}
