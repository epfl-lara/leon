package funcheck

import scala.tools.nsc._

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait Extractors {
  val global: Global
  val pluginInstance: FunCheckPlugin

  import global._
  import global.definitions._

  object StructuralExtractors {
    object ScalaPredef {
      /** Extracts method calls from scala.Predef. */
      def unapply(tree: Tree): Option[String] = tree match {
        case Select(Select(This(scalaName),predefName),symName)
          if("scala".equals(scalaName.toString) && "Predef".equals(predefName.toString)) =>
            Some(symName.toString)
        case _ => None
      }
    }

    object ExEnsuredExpression {
      /** Extracts the 'ensuring' contract from an expression. */
      def unapply(tree: Tree): Option[(Tree,String,Tree)] = tree match {
        case Apply(
          Select(
            Apply(
              TypeApply(
                ScalaPredef("any2Ensuring"),
                TypeTree() :: Nil),
              body :: Nil),
            ensuringName),
          (anonymousFun @ Function(ValDef(_, resultName, resultType, EmptyTree) :: Nil,
            contractBody)) :: Nil)
          if("ensuring".equals(ensuringName.toString)) => Some((body, resultName.toString, contractBody))
        case _ => None
      }
    }

    object ExRequiredExpression {
      /** Extracts the 'require' contract from an expression (only if it's the
       * first call in the block). */
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Block(Apply(ScalaPredef("require"), contractBody :: Nil) :: Nil, body) =>
          Some((body,contractBody))
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
      def unapply(cd: ClassDef): Option[(String,Symbol,Tree)] = cd match {
        case ClassDef(_, name, tparams, impl) if (cd.symbol.isCase && !cd.symbol.isAbstractClass && tparams.isEmpty && impl.body.size >= 8) => {
          impl.children.filter(child => child match {
            case DefDef(_, nn, _, _, _, _) => true
            case _ => false
          }).foreach(child => println(child))
          Some((name.toString, cd.symbol, impl))
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
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(name.toString == "<init>" && tparams.isEmpty && vparamss.size == 1 && vparamss(0).size == 0) => true
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
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(tparams.isEmpty && vparamss.size == 1) => Some((name.toString, vparamss(0), tpt, rhs))
        case _ => None
      }
    }
  }

  object ExpressionExtractors {
    object ExIfThenElse {
      def unapply(tree: Tree): Option[(Tree,Tree,Tree)] = tree match {
        case If(t1,t2,t3) => Some((t1,t2,t3))
        case _ => None
      }
    }

    object ExBooleanLiteral {
      def unapply(tree: Tree): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: Tree): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == IntClass.tpe => Some(c.intValue)
        case _ => None
      }
    }

    object ExIdentifier {
      def unapply(tree: Tree): Option[(String,Tree)] = tree match {
        case i: Ident => Some((i.symbol.name.toString, i))
        case _ => None
      }
    }

    object ExIntIdentifier {
      def unapply(tree: Tree): Option[String] = tree match {
        case i: Ident if i.symbol.tpe == IntClass.tpe => Some(i.symbol.name.toString)
        case _ => None
      }
    }

    object ExAnd {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_and) =>
          Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExOr {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if (s.symbol == Boolean_or) =>
          Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExNot {
      def unapply(tree: Tree): Option[Tree] = tree match {
        case Select(t, n) if (n == nme.UNARY_!) => Some(t)
        case _ => None
      }
    }
  
    object ExEquals {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.EQ) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExNotEquals {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.NE) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExLessThan {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.LT) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExLessEqThan {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.LE) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExGreaterThan {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.GT) => Some((lhs,rhs))
        case _ => None
      }
    }
  
    object ExGreaterEqThan {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.GE) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExUMinus {
      def unapply(tree: Tree): Option[Tree] = tree match {
        case Select(t, n) if (n == nme.UNARY_-) => Some(t)
        case _ => None
      }
    }

    object ExPlus {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.ADD) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExMinus {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.SUB) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExTimes {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.MUL) => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExDiv {
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if (n == nme.DIV) => Some((lhs,rhs))
        case _ => None
      }
    }
  }

  object TypeExtractors {

  }
}
