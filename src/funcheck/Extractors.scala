package funcheck

import scala.tools.nsc._

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait Extractors {
  val global: Global
  val pluginInstance: PluginBase

  import global._
  import global.definitions._

  private lazy val setTraitSym = definitions.getClass("scala.collection.immutable.Set")
  private lazy val multisetTraitSym = definitions.getClass("scala.collection.immutable.Multiset")

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
        case Select(Apply(Select(Select(funcheckIdent, utilsName), any2IsValidName), realExpr :: Nil), holdsName) if (
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

    object ExValDef {
      /** Extracts val's in the head of blocks. */
      def unapply(tree: Block): Option[(Symbol,Tree,Tree,Tree)] = tree match {
        case Block((vd @ ValDef(_, _, tpt, rhs)) :: rest, expr) => 
          if(rest.isEmpty)
            Some((vd.symbol, tpt, rhs, expr))
          else
            Some((vd.symbol, tpt, rhs, Block(rest, expr)))
        case _ => None
      }
    }

    object ExSkipTree {
      /** Skips the first tree in a block */
      def unapply(tree: Block): Option[Tree] = tree match {
        case Block(t :: ts, expr) =>
          if (ts.isEmpty)
            Some(expr)
          else
            Some(Block(ts, expr))
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

    object ExLocalCall {
      def unapply(tree: Apply): Option[(Symbol,String,List[Tree])] = tree match {
        case a @ Apply(Select(This(_), nme), args) => Some((a.symbol, nme.toString, args))
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

    object ExFiniteSet {
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
              collectionName.toString == "collection" && immutableName.toString == "immutable" && setName.toString == "Set" && emptyName.toString == "apply"
            )=> Some(theTypeTree, args)
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

    object ExUnion {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.PLUSPLUS) => Some((lhs,rhs))
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
  }
}
