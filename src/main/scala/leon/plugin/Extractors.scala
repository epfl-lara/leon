package leon
package plugin

import scala.tools.nsc._

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait Extractors {
  val global: Global
  val pluginInstance: LeonPlugin

  import global._
  import global.definitions._

  protected lazy val tuple2Sym: Symbol = definitions.getClass("scala.Tuple2")
  protected lazy val tuple3Sym: Symbol = definitions.getClass("scala.Tuple3")
  protected lazy val tuple4Sym: Symbol = definitions.getClass("scala.Tuple4")
  protected lazy val tuple5Sym: Symbol = definitions.getClass("scala.Tuple5")
  private lazy val setTraitSym = definitions.getClass("scala.collection.immutable.Set")
  private lazy val mapTraitSym = definitions.getClass("scala.collection.immutable.Map")
  private lazy val multisetTraitSym = definitions.getClass("scala.collection.immutable.Multiset")
  private lazy val optionClassSym = definitions.getClass("scala.Option")

  object StructuralExtractors {
    object ScalaPredef {
      /** Extracts method calls from scala.Predef. */
      def unapply(tree: Select): Option[String] = tree match {
        case Select(Select(This(scalaName),predefName),symName)
          if("scala".equals(scalaName.toString) && "Predef".equals(predefName.toString)) =>
            Some(symName.toString)
        case _ => None
      }
    }

    object ExEnsuredExpression {
      /** Extracts the 'ensuring' contract from an expression. */
      def unapply(tree: Apply): Option[(Tree,Symbol,Tree)] = tree match {
        case Apply(
          Select(
            Apply(
              TypeApply(
                ScalaPredef("any2Ensuring"),
                TypeTree() :: Nil),
              body :: Nil),
            ensuringName),
          (Function((vd @ ValDef(_, _, _, EmptyTree)) :: Nil, contractBody)) :: Nil)
          if("ensuring".equals(ensuringName.toString)) => Some((body, vd.symbol, contractBody))
        case _ => None
      }
    }

    object ExHoldsExpression {
      def unapply(tree: Select) : Option[Tree] = tree match {
        case Select(Apply(Select(Select(leonIdent, utilsName), any2IsValidName), realExpr :: Nil), holdsName) if (
          utilsName.toString == "Utils" &&
          any2IsValidName.toString == "any2IsValid" &&
          holdsName.toString == "holds") => Some(realExpr)
        case _ => None
      }        
    }

    object ExRequiredExpression {
      /** Extracts the 'require' contract from an expression (only if it's the
       * first call in the block). */
      def unapply(tree: Block): Option[(Tree,Tree)] = tree match {
        case Block(Apply(ScalaPredef("require"), contractBody :: Nil) :: rest, body) =>
          if(rest.isEmpty)
            Some((body,contractBody))
          else
            Some((Block(rest,body),contractBody))
        case _ => None
      }
    }


    object ExObjectDef {
      /** Matches an object with no type parameters, and regardless of its
       * visibility. Does not match on the automatically generated companion
       * objects of case classes (or any synthetic class). */
      def unapply(cd: ClassDef): Option[(String,Template)] = cd match {
        case ClassDef(_, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty && !cd.symbol.isSynthetic) => {
          Some((name.toString, impl))
        }
        case _ => None
      }
    }

    object ExAbstractClass {
      /** Matches an abstract class or a trait with no type parameters, no
       * constrctor args (in the case of a class), no implementation details,
       * no abstract members. */
      def unapply(cd: ClassDef): Option[(String,Symbol)] = cd match {
        // abstract class
        case ClassDef(_, name, tparams, impl) if (cd.symbol.isAbstractClass && tparams.isEmpty && impl.body.size == 1) => Some((name.toString, cd.symbol))

        case _ => None
      }
    }

    object ExCaseClass {
      def unapply(cd: ClassDef): Option[(String,Symbol,Seq[(String,Tree)])] = cd match {
        case ClassDef(_, name, tparams, impl) if (cd.symbol.isCase && !cd.symbol.isAbstractClass && tparams.isEmpty && impl.body.size >= 8) => {
          val constructor: DefDef = impl.children.find(child => child match {
            case ExConstructorDef() => true
            case _ => false
          }).get.asInstanceOf[DefDef]

          val args = constructor.vparamss(0).map(vd => (vd.name.toString, vd.tpt))

          Some((name.toString, cd.symbol, args))
        }
        case _ => None
      }
    }

    object ExCaseClassSyntheticJunk {
      def unapply(cd: ClassDef): Boolean = cd match {
        case ClassDef(_, _, _, _) if (cd.symbol.isSynthetic && cd.symbol.isFinal) => true
        case _ => false
      }
    }

    object ExConstructorDef {
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(name == nme.CONSTRUCTOR && tparams.isEmpty && vparamss.size == 1) => true
        case _ => false
      }
    }

    object ExMainFunctionDef {
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(name.toString == "main" && tparams.isEmpty && vparamss.size == 1 && vparamss(0).size == 1) => {
          true
        }
        case _ => false
      }
    }

    object ExFunctionDef {
      /** Matches a function with a single list of arguments, no type
       * parameters and regardless of its visibility. */
      def unapply(dd: DefDef): Option[(String,Seq[ValDef],Tree,Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(tparams.isEmpty && vparamss.size == 1 && name != nme.CONSTRUCTOR) => Some((name.toString, vparamss(0), tpt, rhs))
        case _ => None
      }
    }

  }

  object ExpressionExtractors {

    //object ExLocalFunctionDef {
    //  def unapply(tree: Block): Option[(DefDef,String,Seq[ValDef],Tree,Tree,Tree)] = tree match {
    //    case Block((dd @ DefDef(_, name, tparams, vparamss, tpt, rhs)) :: rest, expr) if(tparams.isEmpty && vparamss.size == 1 && name != nme.CONSTRUCTOR) => {
    //      if(rest.isEmpty)
    //        Some((dd,name.toString, vparamss(0), tpt, rhs, expr))
    //      else
    //        Some((dd,name.toString, vparamss(0), tpt, rhs, Block(rest, expr)))
    //    } 
    //    case _ => None
    //  }
    //}


    object ExEpsilonExpression {
      def unapply(tree: Apply) : Option[(Type, Symbol, Tree)] = tree match {
        case Apply(
              TypeApply(Select(Select(funcheckIdent, utilsName), epsilonName), typeTree :: Nil),
              Function((vd @ ValDef(_, _, _, EmptyTree)) :: Nil, predicateBody) :: Nil) => {
          if (utilsName.toString == "Utils" && epsilonName.toString == "epsilon")
            Some((typeTree.tpe, vd.symbol, predicateBody))
          else 
            None
        }
        case _ => None
      }
    }


    object ExValDef {
      /** Extracts val's in the head of blocks. */
      def unapply(tree: ValDef): Option[(Symbol,Tree,Tree)] = tree match {
        case vd @ ValDef(mods, _, tpt, rhs) if !mods.isMutable => Some((vd.symbol, tpt, rhs))
        case _ => None
      }
    }
    object ExVarDef {
      /** Extracts var's in the head of blocks. */
      def unapply(tree: ValDef): Option[(Symbol,Tree,Tree)] = tree match {
        case vd @ ValDef(mods, _, tpt, rhs) if mods.isMutable => Some((vd.symbol, tpt, rhs))
        case _ => None
      }
    }

    object ExAssign {
      def unapply(tree: Assign): Option[(Symbol,Tree)] = tree match {
        case Assign(id@Ident(_), rhs) => Some((id.symbol, rhs))
        case _ => None
      }
    }

    object ExWhile {
      def unapply(tree: LabelDef): Option[(Tree,Tree)] = tree match {
        case (label@LabelDef(
                _, _, If(cond, Block(body, jump@Apply(_, _)), unit@ExUnitLiteral())))
              if label.symbol == jump.symbol && unit.symbol == null => Some((cond, Block(body, unit)))
        case _ => None
      }
    }
    object ExWhileWithInvariant {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
          Select(
            Apply(while2invariant, List(ExWhile(cond, body))),
            invariantSym),
          List(invariant)) if invariantSym.toString == "invariant" => Some((cond, body, invariant))
        case _ => None
      }
    }
    object ExTuple {
      def unapply(tree: Apply): Option[(Seq[Type], Seq[Tree])] = tree match {
        case Apply(
          Select(New(tupleType), _),
          List(e1, e2)
        ) if tupleType.symbol == tuple2Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2)) => Some((Seq(t1, t2), Seq(e1, e2)))
            case _ => None
          }

        case Apply(
          Select(New(tupleType), _),
          List(e1, e2, e3)
        ) if tupleType.symbol == tuple3Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2, t3)) => Some((Seq(t1, t2, t3), Seq(e1, e2, e3)))
            case _ => None
          }
        case Apply(
          Select(New(tupleType), _),
          List(e1, e2, e3, e4)
        ) if tupleType.symbol == tuple4Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2, t3, t4)) => Some((Seq(t1, t2, t3, t4), Seq(e1, e2, e3, e4)))
            case _ => None
          }
        case Apply(
          Select(New(tupleType), _),
          List(e1, e2, e3, e4, e5)
        ) if tupleType.symbol == tuple5Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2, t3, t4, t5)) => Some((Seq(t1, t2, t3, t4, t5), Seq(e1, e2, e3, e4, e5)))
            case _ => None
          }
        case _ => None
      }
    }

    object ExTupleExtract {
      def unapply(tree: Select) : Option[(Tree,Int)] = tree match {
        case Select(lhs, n) => {
          val methodName = n.toString
          if(methodName.head == '_') {
            val indexString = methodName.tail
            try {
              val index = indexString.toInt
              if(index > 0) {
                Some((lhs, index)) 
              } else None
            } catch {
              case _ => None
            }
          } else None
        }
        case _ => None
      }
    }

    object ExIfThenElse {
      def unapply(tree: If): Option[(Tree,Tree,Tree)] = tree match {
        case If(t1,t2,t3) => Some((t1,t2,t3))
        case _ => None
      }
    }

    object ExBooleanLiteral {
      def unapply(tree: Literal): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == IntClass.tpe => Some(c.intValue)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe == UnitClass.tpe => true
        case _ => false
      }
    }

    object ExSomeConstruction {
      def unapply(tree: Apply) : Option[(Type,Tree)] = tree match {
        case Apply(s @ Select(New(tpt), n), arg) if (arg.size == 1 && n == nme.CONSTRUCTOR && tpt.symbol.name.toString == "Some") => tpt.tpe match {
          case TypeRef(_, sym, tpe :: Nil) => Some((tpe, arg(0)))
          case _ => None
        }
        case _ => None
      }
    }

    object ExCaseClassConstruction {
      def unapply(tree: Apply): Option[(Tree,Seq[Tree])] = tree match {
        case Apply(s @ Select(New(tpt), n), args) if (n == nme.CONSTRUCTOR) => {
          Some((tpt, args))
        }
        case _ => None
      }
    }

    object ExIdentifier {
      def unapply(tree: Ident): Option[(Symbol,Tree)] = tree match {
        case i: Ident => Some((i.symbol, i))
        case _ => None
      }
    }

    object ExTyped {
      def unapply(tree : Typed): Option[(Tree,Tree)] = tree match {
        case Typed(e,t) => Some((e,t))
        case _ => None
      }
    }

    object ExIntIdentifier {
      def unapply(tree: Ident): Option[String] = tree match {
        case i: Ident if i.symbol.tpe == IntClass.tpe => Some(i.symbol.name.toString)
        case _ => None
      }
    }

    object ExAnd {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_and) =>
          Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExOr {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_or) =>
          Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExNot {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if (n == nme.UNARY_!) => Some(t)
        case _ => None
      }
    }
  
    object ExEquals {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.EQ) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExNotEquals {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.NE) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExLessThan {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.LT) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExLessEqThan {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.LE) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExGreaterThan {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.GT) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExGreaterEqThan {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.GE) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExUMinus {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if (n == nme.UNARY_-) => Some(t)
        case _ => None
      }
    }

    object ExPlus {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.ADD) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExMinus {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.SUB) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExTimes {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.MUL) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExDiv {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.DIV) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExMod {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.MOD) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExLocalCall {
      def unapply(tree: Apply): Option[(Symbol,String,List[Tree])] = tree match {
        case a @ Apply(Select(This(_), nme), args) => Some((a.symbol, nme.toString, args))
        case a @ Apply(Ident(nme), args) => Some((a.symbol, nme.toString, args))
        case _ => None
      }
    }

    // used for case classes selectors.
    object ExParameterlessMethodCall {
      def unapply(tree: Select): Option[(Tree,Name)] = tree match {
        case Select(lhs, n) => Some((lhs, n))
        case _ => None
      }
    }

    object ExPatternMatching {
      def unapply(tree: Match): Option[(Tree,List[CaseDef])] =
        if(tree != null) Some((tree.selector, tree.cases)) else None
    }

    object ExSetMin {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(
          TypeApply(Select(setTree, minName), typeTree :: Nil),
          ordering :: Nil) if minName.toString == "min" && typeTree.tpe == IntClass.tpe => Some(setTree)
        case _ => None
      }
    }

    object ExSetMax {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(
          TypeApply(Select(setTree, maxName), typeTree :: Nil),
          ordering :: Nil) if maxName.toString == "max" && typeTree.tpe == IntClass.tpe => Some(setTree)
        case _ => None
      }
    }

    object ExEmptySet {
      def unapply(tree: TypeApply): Option[Tree] = tree match {
        case TypeApply(
          Select(
            Select(
              Select(
                Select(Ident(s), collectionName),
                immutableName),
              setName),
            emptyName),  theTypeTree :: Nil) if (
            collectionName.toString == "collection" && immutableName.toString == "immutable" && setName.toString == "Set" && emptyName.toString == "empty"
          ) => Some(theTypeTree)
        case TypeApply(Select(Select(Select(This(scalaName), predefName), setname), applyName), theTypeTree :: Nil)  if ("scala".equals(scalaName.toString) && "Predef".equals(predefName.toString) && "empty".equals(applyName.toString)) => Some(theTypeTree)
        case _ => None
      }
    }

    object ExEmptyMultiset {
      def unapply(tree: TypeApply): Option[Tree] = tree match {
        case TypeApply(
          Select(
            Select(
              Select(
                Select(Ident(s), collectionName),
                immutableName),
              setName),
            emptyName),  theTypeTree :: Nil) if (
            collectionName.toString == "collection" && immutableName.toString == "immutable" && setName.toString == "Multiset" && emptyName.toString == "empty"
          ) => Some(theTypeTree)
        case _ => None
      }
    }

    object ExEmptyMap {
      def unapply(tree: TypeApply): Option[(Tree,Tree)] = tree match {
        case TypeApply(
          Select(
            Select(
              Select(
                Select(Ident(s), collectionName),
                immutableName),
              mapName),
            emptyName), fromTypeTree :: toTypeTree :: Nil) if (
            collectionName.toString == "collection" && immutableName.toString == "immutable" && mapName.toString == "Map" && emptyName.toString == "empty"
          ) => Some((fromTypeTree, toTypeTree))
        case TypeApply(Select(Select(Select(This(scalaName), predefName), mapName), emptyName), fromTypeTree :: toTypeTree :: Nil) if (scalaName.toString == "scala" && predefName.toString == "Predef" && emptyName.toString == "empty") => Some((fromTypeTree, toTypeTree))
        case _ => None
      }
    }

    object ExFiniteSet {
      def unapply(tree: Apply): Option[(Tree,List[Tree])] = tree match {
        case Apply(TypeApply(Select(Select(Select(Select(Ident(s), collectionName), immutableName), setName), applyName), theTypeTree :: Nil), args) if (collectionName.toString == "collection" && immutableName.toString == "immutable" && setName.toString == "Set" && applyName.toString == "apply") => Some((theTypeTree, args))
        case Apply(TypeApply(Select(Select(Select(This(scalaName), predefName), setName), applyName), theTypeTree :: Nil), args) if ("scala".equals(scalaName.toString) && "Predef".equals(predefName.toString) && setName.toString == "Set" && "apply".equals(applyName.toString)) => Some((theTypeTree, args))
        case _ => None
      }
    }

    object ExFiniteMultiset {
      def unapply(tree: Apply): Option[(Tree,List[Tree])] = tree match {
        case Apply(
          TypeApply(
            Select(
              Select(
                Select(
                  Select(Ident(s), collectionName),
                  immutableName),
                setName),
              emptyName),  theTypeTree :: Nil), args) if (
              collectionName.toString == "collection" && immutableName.toString == "immutable" && setName.toString == "Multiset" && emptyName.toString == "apply"
            )=> Some(theTypeTree, args)
        case _ => None
      }
    }

    // object ExFiniteMap {
    //   def unapply(tree: Apply): Option[(Tree,Tree,List[Tree])] = tree match {
    //     case Apply(TypeApply(Select(Select(Select(Select(Ident(s), collectionName), immutableName), mapName), applyName), List(fromTypeTree, toTypeTree)), args) if (collectionName.toString == "collection" && immutableName.toString == "immutable" && mapName.toString == "Map" && applyName.toString == "apply") => Some((fromTypeTree, toTypeTree, args))
    //     case Apply(TypeApply(Select(Select(Select(This(scalaName), predefName), mapName), applyName), List(fromTypeTree, toTypeTree)), args) if (scalaName.toString == "scala" && predefName.toString == "Predef" && mapName.toString == "Map" && applyName.toString == "apply") => Some((fromTypeTree, toTypeTree, args))
    //     case _ => None
    //   }
    // }

    object ExUnion {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == encode("++")/*nme.PLUSPLUS*/) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExPlusPlusPlus {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n.toString == "$plus$plus$plus") => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExIntersection {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == encode("**")) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExSetContains {
      def unapply(tree: Apply) : Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n.toString == "contains") => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExSetSubset {
      def unapply(tree: Apply) : Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n.toString == "subsetOf") => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExSetMinus {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == encode("--")) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExSetCard {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if (n.toString == "size") => Some(t)
        case _ => None
      }
    }

    object ExMultisetToSet {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if (n.toString == "toSet") => Some(t)
        case _ => None
      }
    }

    object ExMapUpdated {
      def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
        case Apply(TypeApply(Select(lhs, n), typeTreeList), List(from, to)) if (n.toString == "updated") => 
          Some((lhs, from, to))
        case _ => None
      }
    }

    object ExApply {
      def unapply(tree: Apply): Option[(Tree,List[Tree])] = tree match {
        case Apply(Select(lhs, n), rhs) if (n.toString == "apply") => Some((lhs, rhs))
        case _ => None
      }
    }

    object ExMapIsDefinedAt {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n.toString == "isDefinedAt") => Some((lhs, rhs))
        case _ => None
      }
    }
  }
}
