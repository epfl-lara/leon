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

    object EnsuredExpression {
      /** Extracts the 'ensuring' contract from an expression. */
      def unapply(tree: Tree): Option[(Tree,Function)] = tree match {
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
          if("ensuring".equals(ensuringName.toString)) => Some((body,anonymousFun))
        case _ => None
      }
    }

    object RequiredExpression {
      /** Extracts the 'require' contract from an expression (only if it's the
       * first call in the block). */
      def unapply(tree: Tree): Option[(Tree,Tree)] = tree match {
        case Block(Apply(ScalaPredef("require"), contractBody :: Nil) :: Nil, body) =>
          Some((body,contractBody))
        case _ => None
      }
    }

    object ObjectDefn {
      /** Matches an object with no type parameters, and regardless of its
       * visibility. */
      def unapply(cd: ClassDef): Option[(String,Template)] = cd match {
        case ClassDef(_, name, tparams, impl) if (cd.symbol.isModuleClass && tparams.isEmpty) => Some((name.toString, impl))
        case _ => None
      }
    }

    object FunctionDefn {
      /** Matches a function with a single list of arguments, no type
       * parameters and regardless of its visibility. */
      def unapply(dd: DefDef): Option[(String,Seq[ValDef],Tree,Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(tparams.isEmpty && vparamss.size == 1) => Some((name.toString, vparamss(0), tpt, rhs))
        case _ => None
      }
    }
  }

  object ExpressionExtractors {
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
  }

  object TypeExtractors {

  }
}
