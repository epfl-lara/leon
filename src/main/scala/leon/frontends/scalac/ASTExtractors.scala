/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc._

/** Contains extractors to pull-out interesting parts of the Scala ASTs. */
trait ASTExtractors {
  val global: Global

  import global._
  import global.definitions._

  def classFromName(str: String) = {
    rootMirror.getClassByName(newTypeName(str))
  }

  def objectFromName(str: String) = {
    rootMirror.getClassByName(newTermName(str))
  }

  def annotationsOf(s: Symbol): Map[String, Seq[Option[Any]]] = {
    val actualSymbol = s.accessedOrSelf

    (for {
      a <- actualSymbol.annotations ++ actualSymbol.owner.annotations
      name = a.atp.safeToString.replaceAll("\\.package\\.", ".")
      if (name startsWith "leon.annotation.")
    } yield {
      val args = a.args.map {
        case Literal(x) => Some(x.value)
        case _ => None
      }
      (name.split("\\.", 3)(2), args)
    }).toMap
  }

  private val integralTypes = Set(ByteTpe, IntTpe)

  protected lazy val tuple2Sym          = classFromName("scala.Tuple2")
  protected lazy val tuple3Sym          = classFromName("scala.Tuple3")
  protected lazy val tuple4Sym          = classFromName("scala.Tuple4")
  protected lazy val tuple5Sym          = classFromName("scala.Tuple5")
  protected lazy val tuple6Sym          = classFromName("scala.Tuple6")
  protected lazy val tuple7Sym          = classFromName("scala.Tuple7")
  protected lazy val tuple8Sym          = classFromName("scala.Tuple8")
  protected lazy val scalaMapSym        = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym        = classFromName("scala.collection.immutable.Set")
  protected lazy val setSym             = classFromName("leon.lang.Set")
  protected lazy val mapSym             = classFromName("leon.lang.Map")
  protected lazy val bagSym             = classFromName("leon.lang.Bag")
  protected lazy val realSym            = classFromName("leon.lang.Real")
  protected lazy val optionClassSym     = classFromName("scala.Option")
  protected lazy val arraySym           = classFromName("scala.Array")
  protected lazy val someClassSym       = classFromName("scala.Some")
  protected lazy val byNameSym          = classFromName("scala.<byname>")
  protected lazy val bigIntSym          = classFromName("scala.math.BigInt")
  protected lazy val stringSym          = classFromName("java.lang.String")
  protected def functionTraitSym(i:Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple2(sym : Symbol) : Boolean = sym == tuple2Sym
  def isTuple3(sym : Symbol) : Boolean = sym == tuple3Sym
  def isTuple4(sym : Symbol) : Boolean = sym == tuple4Sym
  def isTuple5(sym : Symbol) : Boolean = sym == tuple5Sym
  def isTuple6(sym : Symbol) : Boolean = sym == tuple6Sym
  def isTuple7(sym : Symbol) : Boolean = sym == tuple7Sym
  def isTuple8(sym : Symbol) : Boolean = sym == tuple8Sym

  def isBigIntSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

  def isByNameSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      getResolvedTypeSym(sym.tpe.resultType.typeSymbol)
    } else {
      sym
    }
  }

  def isSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == setSym
  }

  def isBagSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bagSym
  }

  def isRealSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == realSym
  }

  def isScalaSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaSetSym
  }

  def isMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mapSym
  }

  def isScalaMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaMapSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction(sym : Symbol, i: Int) : Boolean =
    0 <= i && i <= 22 && sym == functionTraitSym(i)

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def hasIntegralType(t : Tree) = {
   val tpe = t.tpe.widen
   integralTypes contains tpe
  }

  def hasBigIntType(t : Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t : Tree) = isStringSym(t.tpe.typeSymbol)

  def hasRealType(t : Tree) = isRealSym(t.tpe.typeSymbol)

  /** A set of helpers for extracting trees.*/
  object ExtractorHelpers {
    /** Extracts the identifier as `"Ident(name)"` (who needs this?!) */
    object ExIdNamed {
      def unapply(id: Ident): Option[String] = Some(id.toString)
    }

    /** Extracts the tree and its type (who needs this?!) */
    object ExHasType {
      def unapply(tr: Tree): Option[(Tree, Symbol)] = Some((tr, tr.tpe.typeSymbol))
    }

    /** Extracts the string representation of a name of something having the `Name` trait */
    object ExNamed {
      def unapply(name: Name): Option[String] = Some(name.toString)
    }

    /** Returns the full dot-separated names of the symbol as a list of strings */
    object ExSymbol {
      def unapplySeq(t: Tree): Option[Seq[String]] = {
        Some(t.symbol.fullName.toString.split('.').toSeq)
      }
    }

    /** Matches nested `Select(Select(...Select(a, b) ...y) , z)` and returns the list `a,b, ... y,z` */
    object ExSelected {
      def unapplySeq(select: Select): Option[Seq[String]] = select match {
        case Select(This(scalaName), name) =>
          Some(Seq(scalaName.toString, name.toString))

        case Select(from: Select, name) =>
          unapplySeq(from).map(prefix => prefix :+ name.toString)

        case Select(from: Ident, name) =>
          Some(Seq(from.toString, name.toString))

        case _ =>
          None
      }
    }
  }

  object StructuralExtractors {
    import ExtractorHelpers._

    /** Extracts the measure function in the `decreases` clause. */
    object ExDecreasesMeasure {
      def unapply(tree: Apply): Option[Tree] = tree match {
        case Apply(ExSelected("leon", "lang", "package", "decreases"), body :: Nil) => Some(body)
        case _ => None
      }
    }

    /** Extracts the 'ensuring' contract from an expression. */
    object ExEnsuredExpression {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(Apply(TypeApply(ExSelected("scala", "Predef", "Ensuring"), _ :: Nil), body :: Nil), ExNamed("ensuring")), contract :: Nil)
          => Some((body, contract))
        case Apply(Select(Apply(TypeApply(ExSelected("leon", "lang", "StaticChecks", "any2Ensuring"), _ :: Nil), body :: Nil), ExNamed("ensuring")), contract :: Nil)
          => Some((body, contract))
        case _ => None
      }
    }

    /** Matches the `holds` expression at the end of any boolean expression, and returns the boolean expression.*/
    object ExHoldsExpression {
      def unapply(tree: Select) : Option[Tree] = tree match {
        case Select(
          Apply(ExSelected("leon", "lang", "package", "BooleanDecorations"), realExpr :: Nil),
          ExNamed("holds")
        ) => Some(realExpr)
        case _ => None
       }
    }

    /** Matches the `holds` expression at the end of any boolean expression with a proof as argument, and returns both of themn.*/
    object ExHoldsWithProofExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(Apply(ExSelected("leon", "lang", "package", "BooleanDecorations"), body :: Nil), ExNamed("holds")), proof :: Nil) =>
          Some((body, proof))
        case _ => None
       }
    }

    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause. If no "because" method, still returns the expression */
    object ExMaybeBecauseExpressionWrapper {
      def unapply(tree: Tree) : Some[Tree] = tree match {
        case Apply(ExSelected("leon", "lang", "package", "because"), body :: Nil) =>
          unapply(body)
        case body => Some(body)
       }
    }

    /** Matches the `because` method at the end of any boolean expression, and return the assertion and the cause.*/
    object ExBecauseExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(Apply(ExSelected("leon", "proof", "package", "boolean2ProofOps"), body :: Nil), ExNamed("because")), proof :: Nil) =>
          Some((body, proof))
        case _ => None
       }
    }

    /** Matches the `bigLength` expression at the end of any string expression, and returns the expression.*/
    object ExBigLengthExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(Select(
          Apply(ExSelected("leon", "lang", "package", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigLength")), Nil)
          => Some(stringExpr)
        case _ => None
       }
    }

    /** Matches the `bigSubstring` method at the end of any string expression, and returns the expression and the start index expression.*/
    object ExBigSubstringExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("leon", "lang", "package", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: Nil)
           => Some(stringExpr, startExpr)
        case _ => None
       }
    }

    /** Matches the `bigSubstring` expression at the end of any string expression, and returns the expression, the start and end index expressions.*/
    object ExBigSubstring2Expression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(ExSelected("leon", "lang", "package", "StringDecorations"), stringExpr :: Nil),
          ExNamed("bigSubstring")), startExpr :: endExpr :: Nil)
           => Some(stringExpr, startExpr, endExpr)
        case _ => None
       }
    }

    /** Matches an implication `lhs ==> rhs` and returns (lhs, rhs)*/
    object ExImplies {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case
          Apply(
            Select(
              Apply(
                ExSelected("leon", "lang", "package", "BooleanDecorations"),
                lhs :: Nil
              ),
              ExNamed("$eq$eq$greater")
            ),
            rhs :: Nil
          ) => Some((lhs, rhs))
        case _ => None
      }
    }

    /** Extracts the 'require' contract from an expression (only if it's the
     * first call in the block). */
    object ExRequiredExpression {
      def unapply(tree: Apply): Option[Tree] = tree match {
        case Apply(ExSelected("scala", "Predef", "require"), contractBody :: Nil) =>
         Some(contractBody)
        case Apply(ExSelected("leon", "lang", "StaticChecks", "require"), contractBody :: Nil) =>
         Some(contractBody)
        case _ => None
      }
    }

    /** Matches the `A computes B` expression at the end of any expression A, and returns (A, B).*/
    object ExComputesExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(Select(
          Apply(TypeApply(ExSelected("leon", "lang", "package", "SpecsDecorations"), List(_)), realExpr :: Nil),
          ExNamed("computes")), expected::Nil)
         => Some((realExpr, expected))
        case _ => None
       }
    }

    /** Matches the `O ask I` expression at the end of any expression O, and returns (I, O).*/
    object ExAskExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(TypeApply(Select(
          Apply(TypeApply(ExSelected("leon", "lang", "package", "SpecsDecorations"), List(_)), output :: Nil),
          ExNamed("ask")), List(_)), input::Nil)
         => Some((input, output))
        case _ => None
       }
    }

    object ExByExampleExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case Apply(TypeApply(ExSelected("leon", "lang", "package", "byExample"), List(_, _)), input :: res_output :: Nil)
         => Some((input, res_output))
        case _ => None
       }
    }

    /** Extracts the `(input, output) passes { case In => Out ...}` and returns (input, output, list of case classes) */
    object ExPasses {
      def unapply(tree : Apply) : Option[(Tree, Tree, List[CaseDef])] = tree match {
        case  Apply(
                Select(
                  Apply(
                    TypeApply(
                      ExSelected("leon", "lang", "package", "Passes"),
                      List(_, _)
                    ),
                    List(ExpressionExtractors.ExTuple(_, Seq(in,out)))
                  ),
                  ExNamed("passes")
                ),
                List(Function(
                  List(ValDef(_, _, _, EmptyTree)),
                  ExpressionExtractors.ExPatternMatching(_,tests)
                ))
              )
          => Some((in, out, tests))
        case _ => None
      }
    }

    /** Returns a string literal from a constant string literal. */
    object ExStringLiteral {
      def unapply(tree: Tree): Option[String] = tree  match {
        case Literal(c @ Constant(i)) if c.tpe == StringClass.tpe =>
          Some(c.stringValue)
        case _ =>
          None
      }
    }

    /** Returns the arguments of an unapply pattern */
    object ExUnapplyPattern {
      def unapply(tree: Tree): Option[(Symbol, Seq[Tree])] = tree match {
        case UnApply(Apply(s, _), args) =>
          Some((s.symbol, args))
        case _ => None
      }
    }

    /** Returns the argument of a bigint literal, either from scala or leon */
    object ExBigIntLiteral {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(ExSelected("scala", "package", "BigInt", "apply"), n :: Nil) =>
          Some(n)
        case Apply(ExSelected("leon", "lang", "package", "BigInt", "apply"), n :: Nil) =>
          Some(n)
        case _ =>
          None
      }
    }

    /** Returns the two components (n, d) of a real n/d literal */
    object ExRealLiteral {
      def unapply(tree: Tree): Option[(Tree, Tree)] = tree  match {
        case Apply(ExSelected("leon", "lang", "Real", "apply"), n :: d :: Nil) =>
          Some((n, d))
        case _ =>
          None
      }
    }

    /** Matches Real(x) when n is an integer and returns x */
    object ExRealIntLiteral {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(ExSelected("leon", "lang", "Real", "apply"), n :: Nil) =>
          Some(n)
        case _ =>
          None
      }
    }

    /** Matches the construct int2bigInt(a) and returns a */
    object ExIntToBigInt {
      def unapply(tree: Tree): Option[Tree] = tree  match {
        case Apply(ExSelected("math", "BigInt", "int2bigInt"), tree :: Nil) => Some(tree)
        case _ => None
      }
    }

    /** Matches the construct List[tpe](a, b, ...) and returns tpe and arguments */
    object ExListLiteral {
      def unapply(tree: Apply): Option[(Tree, List[Tree])] = tree  match {
        case Apply(
              TypeApply(ExSelected("leon", "collection", "List", "apply"), tpe :: Nil),
              args) =>
          Some((tpe, args))
        case _ =>
          None
      }
    }

    /** Extracts the 'assert' contract from an expression (only if it's the
      * first call in the block). */
    object ExAssertExpression {
      def unapply(tree: Apply): Option[(Tree, Option[String])] = tree match {
        case Apply(ExSelected("scala", "Predef", "assert"), contractBody :: Nil) =>
         Some((contractBody, None))
        case Apply(ExSelected("scala", "Predef", "assert"), contractBody :: (error: Literal) :: Nil) =>
         Some((contractBody, Some(error.value.stringValue)))
        case Apply(ExSelected("leon", "lang", "StaticChecks", "assert"), contractBody :: Nil) =>
         Some((contractBody, None))
        case _ =>
         None
      }
    }

    /** Matches an object with no type parameters, and regardless of its
      * visibility. Does not match on case objects or the automatically generated companion
      * objects of case classes (or any synthetic class). */
    object ExObjectDef {
      def unapply(cd: ClassDef): Option[(String,Template)] = cd match {
        case ClassDef(_, name, tparams, impl) if
          (cd.symbol.isModuleClass || cd.symbol.hasPackageFlag) &&
          tparams.isEmpty &&
          !cd.symbol.isSynthetic &&
          !cd.symbol.isCaseClass
        => {
          Some((name.toString, impl))
        }
        case _ => None
      }
    }

    /** Matches an abstract class or a trait with no type parameters, no
      * constructor args (in the case of a class), no implementation details,
      * no abstract members. */
    object ExAbstractClass {
      def unapply(cd: ClassDef): Option[(String, Symbol, Template)] = cd match {
        // abstract class
        case ClassDef(_, name, tparams, impl) if cd.symbol.isAbstractClass => Some((name.toString, cd.symbol, impl))

        case _ => None
      }
    }

    /** Returns true if the class definition is a case class */
    private def isCaseClass(cd: ClassDef): Boolean = {
      cd.symbol.isCase && !cd.symbol.isAbstractClass && cd.impl.body.size >= 8
    }

    /** Returns true if the class definition is an implicit class */
    private def isImplicitClass(cd: ClassDef): Boolean = {
      cd.symbol.isImplicit
    }

    object ExCaseClass {
      def unapply(cd: ClassDef): Option[(String,Symbol,Seq[(Symbol,ValDef)], Template)] = cd match {
        case ClassDef(_, name, tparams, impl) if isCaseClass(cd) || isImplicitClass(cd) => {
          val constructor: DefDef = impl.children.find {
            case ExConstructorDef() => true
            case _ => false
          }.get.asInstanceOf[DefDef]
          //println("extract constructor: " + constructor)

          val valDefs = constructor.vparamss.flatten
          //println("valDefs: " + valDefs)

          //valDefs.foreach(vd => println(vd.symbol.tpe.toString == "Test.Mutable[A]"))

          //if(valDefs.exists(vd => vd.symbol.tpe.toString == "Test.Mutable[A]")) {
          //  println("found evidence")
          //  println(name)
          //}

          //impl.children foreach println

          val symbols = impl.children.collect {
            case df@DefDef(_, name, _, _, _, _) if
              df.symbol.isAccessor && df.symbol.isParamAccessor
              && !name.endsWith("_$eq") => df.symbol
          }
          //println("symbols: " + symbols)
          //println("symbols accessed: " + symbols.map(_.accessed))

          //if (symbols.size != valDefs.size) {
          //  println(" >>>>> " + cd.name)
          //  symbols foreach println
          //  valDefs foreach println
          //}

          val args = symbols zip valDefs
          //if(valDefs.exists(vd => vd.symbol.tpe.toString == "Test.Mutable[A]")) {
          //  println("symbols: " + symbols)
          //  println("args: " + args)
          //}

          Some((name.toString, cd.symbol, args, impl))
        }
        case _ => None
      }
    }

    object ExCaseObject {
      def unapply(s: Select): Option[Symbol] = {
        if (s.tpe.typeSymbol.isModuleClass) {
          Some(s.tpe.typeSymbol)
        } else {
          None
        }
      }
    }

    object ExCompanionObjectSynthetic {
      def unapply(cd : ClassDef) : Option[(String, Symbol, Template)] = {
        val sym = cd.symbol
        cd match {
         case ClassDef(_, name, tparams, impl) if sym.isModule && sym.isSynthetic => //FIXME flags?
           Some((name.toString, sym, impl))
         case _ => None
        }

      }
    }

    object ExCaseClassSyntheticJunk {
      def unapply(cd: Tree): Boolean = cd match {
        case ClassDef(_, _, _, _) if cd.symbol.isSynthetic => true
        case DefDef(_, _, _, _, _, _) if cd.symbol.isSynthetic && (cd.symbol.isCase || cd.symbol.isPrivate) => true
        case _ => false
      }
    }

    object ExConstructorDef {
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name == nme.CONSTRUCTOR && tparams.isEmpty => true
        case _ => false
      }
    }

    object ExMainFunctionDef {
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name.toString == "main" && tparams.isEmpty && vparamss.size == 1 && vparamss.head.size == 1 => {
          true
        }
        case _ => false
      }
    }

    object ExFunctionDef {
      /** Matches a function with a single list of arguments,
        * and regardless of its visibility.
        */
      def unapply(dd: DefDef): Option[(Symbol, Seq[Symbol], Seq[ValDef], Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if name != nme.CONSTRUCTOR && !dd.symbol.isAccessor =>
          if (dd.symbol.isSynthetic && dd.symbol.isImplicit && dd.symbol.isMethod) {
            // Check that the class it was generated from is not ignored
            if (annotationsOf(tpt.symbol).isDefinedAt("ignore")) {
              None
            } else {
              Some((dd.symbol, tparams.map(_.symbol), vparamss.flatten, tpt.tpe, rhs))
            }
          } else if (!dd.symbol.isSynthetic) {
            Some((dd.symbol, tparams.map(_.symbol), vparamss.flatten, tpt.tpe, rhs))
          } else {
            None
          }
        case _ => None
      }
    }

    object ExLazyAccessorFunction {
      def unapply(dd: DefDef): Option[(Symbol, Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          !dd.symbol.isSynthetic && dd.symbol.isAccessor && dd.symbol.isLazy
        ) =>
          Some((dd.symbol, tpt.tpe, rhs))
        case _ => None
      }
    }

    object ExMutatorAccessorFunction {
      def unapply(dd: DefDef): Option[(Symbol, Seq[Symbol], Seq[ValDef], Type, Tree)] = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          !dd.symbol.isSynthetic && dd.symbol.isAccessor && name.endsWith("_$eq")
        ) =>
          Some((dd.symbol, tparams.map(_.symbol), vparamss.flatten, tpt.tpe, rhs))
        case _ => None
      }
    }
    object ExMutableFieldDef {

      /** Matches a definition of a strict var field inside a class constructor */
      def unapply(vd: SymTree) : Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          // Implemented fields
          case ValDef(mods, name, tpt, rhs) if (
            !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isLazy && !sym.isSynthetic && !sym.isAccessor && sym.isVar
          ) =>
            println("matched a var accessor field: sym is: " + sym)
            println("getterIn is: " + sym.getterIn(sym.owner))
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            Some( (sym.getterIn(sym.owner),tpt.tpe,rhs) )
          case _ => None
        }
      }
    }

    object ExFieldDef {
      /** Matches a definition of a strict field inside a class constructor */
      def unapply(vd: SymTree) : Option[(Symbol, Type, Tree)] = {
        val sym = vd.symbol
        vd match {
          // Implemented fields
          case ValDef(mods, name, tpt, rhs) if (
            !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isLazy && !sym.isSynthetic && !sym.isAccessor && !sym.isVar
          ) =>
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            Some( (sym.getterIn(sym.owner),tpt.tpe,rhs) )
          // Unimplemented fields
          case df@DefDef(_, name, _, _, tpt, _) if (
            sym.isStable && sym.isAccessor && sym.name != nme.CONSTRUCTOR &&
            sym.accessed == NoSymbol // This is to exclude fields with implementation
          ) =>
            Some( (sym, tpt.tpe, EmptyTree))
          case _ => None
        }
      }
    }

    object ExLazyFieldDef {
      /** Matches lazy field definitions.
       *  WARNING: Do NOT use this as extractor for lazy fields,
       *  as it does not contain the body of the lazy definition.
       *  It is here just to signify a Definition acceptable by Leon
       */
      def unapply(vd : ValDef) : Boolean = {
        val sym = vd.symbol
        vd match {
          case ValDef(mods, name, tpt, rhs) if (
            sym.isLazy && !sym.isCaseAccessor && !sym.isParamAccessor &&
            !sym.isSynthetic && !sym.isAccessor
          ) =>
            // Since scalac uses the accessor symbol all over the place, we pass that instead:
            true
          case _ => false
        }
      }
    }

    object ExFieldAccessorFunction{
      /** Matches the accessor function of a field
       *  WARNING: This is not meant to be used for any useful purpose,
       *  other than to satisfy Definition acceptable by Leon
       */
      def unapply(dd: DefDef): Boolean = dd match {
        case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          dd.symbol.isAccessor && !dd.symbol.isLazy
        ) =>
          true
        case _ => false
      }
    }

    object ExDefaultValueFunction{
      /** Matches a function that defines the default value of a parameter */
      def unapply(dd: DefDef): Option[(Symbol, Seq[Symbol], Seq[ValDef], Type, String, Int, Tree)] = {
        val sym = dd.symbol
        dd match {
          case DefDef(_, name, tparams, vparamss, tpt, rhs) if(
            vparamss.size <= 1 && name != nme.CONSTRUCTOR && sym.isSynthetic
          ) =>

            // Split the name into pieces, to find owner of the parameter + param.index
            // Form has to be <owner name>$default$<param index>
            val symPieces = sym.name.toString.reverse.split("\\$", 3).reverseMap(_.reverse)

            try {
              if (symPieces(1) != "default" || symPieces(0) == "copy") throw new IllegalArgumentException("")
              val ownerString = symPieces(0)
              val index = symPieces(2).toInt - 1
              Some((sym, tparams.map(_.symbol), vparamss.headOption.getOrElse(Nil), tpt.tpe, ownerString, index, rhs))
            } catch {
              case _ : NumberFormatException | _ : IllegalArgumentException | _ : ArrayIndexOutOfBoundsException =>
                None
            }

          case _ => None
        }
      }
    }

  }

  object ExpressionExtractors {
    import ExtractorHelpers._

    object ExEpsilonExpression {
      def unapply(tree: Apply) : Option[(Tree, Symbol, Tree)] = tree match {
        case Apply(
              TypeApply(ExSymbol("leon", "lang", "xlang", "epsilon"), typeTree :: Nil),
              Function((vd @ ValDef(_, _, _, EmptyTree)) :: Nil, predicateBody) :: Nil) =>
            Some((typeTree, vd.symbol, predicateBody))
        case _ => None
      }
    }

    object ExErrorExpression {
      def unapply(tree: Apply) : Option[(String, Tree)] = tree match {
        case a @ Apply(TypeApply(ExSymbol("leon", "lang", "error"), List(tpe)), List(lit : Literal)) =>
          Some((lit.value.stringValue, tpe))
        case _ =>
          None
      }
    }

    object ExOldExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case a @ Apply(TypeApply(ExSymbol("leon", "lang", "old"), List(tpe)), List(arg)) =>
          Some(arg)
        case _ =>
          None
      }
    }

    object ExHoleExpression {
      def unapply(tree: Tree) : Option[(Tree, List[Tree])] = tree match {
        case a @ Apply(TypeApply(s @ ExSymbol("leon", "lang", "synthesis", "$qmark"), List(tpt)), args1)  =>
            Some((tpt, args1))
        case TypeApply(s @ ExSymbol("leon", "lang", "synthesis", "$qmark$qmark$qmark"), List(tpt)) =>
            Some((tpt, Nil))
        case _ => None
      }
    }

    object ExChooseExpression {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case a @ Apply(
              TypeApply(s @ ExSymbol("leon", "lang", "synthesis", "choose"), types),
              predicate :: Nil) =>
            Some(predicate)
        case _ => None
      }
    }

    object ExWithOracleExpression {
      def unapply(tree: Apply) : Option[(List[(Tree, Symbol)], Tree)] = tree match {
        case a @ Apply(
              TypeApply(s @ ExSymbol("leon", "lang", "synthesis", "withOracle"), types),
              Function(vds, body) :: Nil) =>
            Some((types zip vds.map(_.symbol), body))
        case _ => None
      }
    }

    object ExLambdaExpression {
      def unapply(tree: Function) : Option[(Seq[ValDef], Tree)] = tree match {
        case Function(vds, body) => Some((vds, body))
        case _ => None
      }
    }

    object ExForallExpression {
      def unapply(tree: Apply) : Option[(List[(Tree, Symbol)], Tree)] = tree match {
        case a @ Apply(
            TypeApply(s @ ExSymbol("leon", "lang", "forall"), types),
            Function(vds, predicateBody) :: Nil) =>
          Some((types zip vds.map(_.symbol), predicateBody))
        case _ => None
      }
    }

    object ExArrayForallExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case a @ Apply(
            TypeApply(s @ ExSymbol("leon", "lang", "arrayForall"), types),
            List(array, pred)) =>
          Some((array, pred))
        case _ => None
      }
    }
    object ExArrayBoundedForallExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree, Tree)] = tree match {
        case a @ Apply(
            TypeApply(s @ ExSymbol("leon", "lang", "arrayForall"), types),
            List(array, from, to, pred)) =>
          Some((array, from, to, pred))
        case _ => None
      }
    }
    object ExBoundedForallExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree)] = tree match {
        case a @ Apply(
            ExSymbol("leon", "lang", "boundedForall"),
            List(from, to, pred)) =>
          Some((from, to, pred))
        case _ => None
      }
    }
    object ExArrayExistsExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree)] = tree match {
        case a @ Apply(
            TypeApply(s @ ExSymbol("leon", "lang", "arrayExists"), types),
            List(array, pred)) =>
          Some((array, pred))
        case _ => None
      }
    }
    object ExArrayBoundedExistsExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree, Tree)] = tree match {
        case a @ Apply(
            TypeApply(s @ ExSymbol("leon", "lang", "arrayExists"), types),
            List(array, from, to, pred)) =>
          Some((array, from, to, pred))
        case _ => None
      }
    }
    object ExBoundedExistsExpression {
      def unapply(tree: Apply) : Option[(Tree, Tree, Tree)] = tree match {
        case a @ Apply(
            ExSymbol("leon", "lang", "boundedExists"),
            List(from, to, pred)) =>
          Some((from, to, pred))
        case _ => None
      }
    }

    object ExArrayUpdated {
      def unapply(tree: Apply): Option[(Tree,Tree,Tree)] = tree match {
        case Apply(
               Apply(
                 TypeApply(
                   Select(
                     Apply(ExSelected("scala", "Predef", s), Seq(lhs)),
                     n
                   ),
                   _
                 ),
                 Seq(index, value)
               ),
               List(Apply(_, _))
             ) if (s.toString contains "Array") &&
                  (n.toString == "updated") =>
          Some((lhs, index, value))
        case Apply(
               Apply(
                 TypeApply(
                   Select(
                     Apply(TypeApply(ExSelected("scala", "Predef", s), tpes), Seq(lhs)),
                     n
                   ),
                   _
                 ),
                 Seq(index, value)
               ),
               List(Apply(_, _))
             ) if (s.toString contains "Array") &&
                  (n.toString == "updated") =>
          Some((lhs, index, value))
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
        //case Assign(sym@Select(This(_), v), rhs) => Some((sym.symbol, rhs))
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

    object ExArrayLiteral {
      def unapply(tree: Apply): Option[(Type, Seq[Tree])] = tree match {
        case Apply(ExSelected("scala", "Array", "apply"), args) =>
          tree.tpe match {
            case TypeRef(_, _, List(t1)) =>
              Some((t1, args))
            case _ =>
              None
          }
        case Apply(Apply(TypeApply(ExSelected("scala", "Array", "apply"), List(tpt)), args), ctags) =>
          Some((tpt.tpe, args))

        case _ =>
          None
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

        case Apply(
          Select(New(tupleType), _),
          List(e1, e2, e3, e4, e5, e6)
        ) if tupleType.symbol == tuple6Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2, t3, t4, t5, t6)) => Some((Seq(t1, t2, t3, t4, t5, t6), Seq(e1, e2, e3, e4, e5, e6)))
            case _ => None
          }

        case Apply(
          Select(New(tupleType), _),
          List(e1, e2, e3, e4, e5, e6, e7)
        ) if tupleType.symbol == tuple7Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2, t3, t4, t5, t6, t7)) => Some((Seq(t1, t2, t3, t4, t5, t6), Seq(e1, e2, e3, e4, e5, e6, e7)))
            case _ => None
          }

        case Apply(
          Select(New(tupleType), _),
          List(e1, e2, e3, e4, e5, e6, e7, e8)
        ) if tupleType.symbol == tuple8Sym => tupleType.tpe match {
            case TypeRef(_, sym, List(t1, t2, t3, t4, t5, t6, t7, t8)) => Some((Seq(t1, t2, t3, t4, t5, t6), Seq(e1, e2, e3, e4, e5, e6, e7, e8)))
            case _ => None
          }

        // Match e1 -> e2
        case Apply(TypeApply(Select(Apply(TypeApply(ExSelected("scala", "Predef", "ArrowAssoc"), List(tpeFrom)), List(from)), ExNamed("$minus$greater")), List(tpeTo)), List(to)) =>

          Some((Seq(tpeFrom.tpe, tpeTo.tpe), Seq(from, to)))
        case _ => None
      }
    }

    object ExLocally {
      def unapply(tree: Apply) : Option[Tree] = tree match {
        case Apply(TypeApply(ExSelected("scala", "Predef", "locally"), _), List(body)) =>
          Some(body)

        case _ =>
          None
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
              case t: Throwable =>
                None
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

    object ExCharLiteral {
      def unapply(tree: Literal): Option[Char] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == CharClass.tpe => Some(c.charValue)
        case _ => None
      }
    }

    object ExByteLiteral {
      def unapply(tree: Literal): Option[Byte] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == ByteTpe => Some(c.byteValue)
        case _ => None
      }
    }

    object ExIntLiteral {
      def unapply(tree: Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe == IntTpe => Some(c.intValue)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe == UnitClass.tpe => true
        case _ => false
      }
    }

    object ExCaseClassConstruction {
      def unapply(tree: Apply): Option[(Tree,Seq[Tree])] = tree match {
        case Apply(s @ Select(New(tpt), n), args) if n == nme.CONSTRUCTOR => {
          Some((tpt, args))
        }
        //essentially this ignores implicit evidence for mutable types annotations
        case Apply(Apply(Select(New(tpt), n), args),
                   List(TypeApply(ExSelected("leon", "lang", "package", "mutable"), _)))
             if n == nme.CONSTRUCTOR => {
          Some((tpt, args))
        }
        case Apply(Apply(Select(New(tpt), n), args),
                   List(s @ Select(qualifier, symbol)))
             if n == nme.CONSTRUCTOR && s.tpe.typeSymbol.fullName == "leon.lang.Mutable" => {
          // s.tpe === TypeRef( SingleType( SingleType( SingleType( ThisType(<root>),  leon),  lang),  package),  Mutable,  [ TypeRef( NoPrefix(),  V,  [ ])])
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
        case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == Boolean_and =>
          Some((lhs,rhs))
        case _ => None
      }
    }

    object ExOr {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(s @ Select(lhs, _), List(rhs)) if s.symbol == Boolean_or =>
          Some((lhs,rhs))
        case _ => None
      }
    }

    object ExNot {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_! => Some(t)
        case _ => None
      }
    }

    object ExEquals {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if n == nme.EQ => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExNotEquals {
      def unapply(tree: Apply): Option[(Tree,Tree)] = tree match {
        case Apply(Select(lhs, n), List(rhs)) if n == nme.NE => Some((lhs,rhs))
        case _ => None
      }
    }

    object ExUMinus {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_- && hasBigIntType(t) => Some(t)
        case _ => None
      }
    }

    object ExRealUMinus {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_- && hasRealType(t) => Some(t)
        case _ => None
      }
    }

    object ExBVUMinus {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_- && hasIntegralType(t) => Some(t)
        case _ => None
      }
    }

    object ExBVNot {
      def unapply(tree: Select): Option[Tree] = tree match {
        case Select(t, n) if n == nme.UNARY_~ && hasIntegralType(t) => Some(t)
        case _ => None
      }
    }

    object ExPatternMatching {
      def unapply(tree: Match): Option[(Tree,List[CaseDef])] =
        if(tree != null) Some((tree.selector, tree.cases)) else None
    }

    object ExBigIntPattern {
      def unapply(tree: UnApply): Option[Tree] = tree match {
        case ua @ UnApply(Apply(ExSelected("leon", "lang", "package", "BigInt", "unapply"), _), List(l)) =>
          Some(l)
        case _ =>
          None
      }
    }

    object ExAsInstanceOf {
      def unapply(tree: TypeApply) : Option[(Tree, Tree)] = tree match {
        case TypeApply(Select(t, isInstanceOfName), typeTree :: Nil) if isInstanceOfName.toString == "asInstanceOf" => Some((t, typeTree))
        case _ => None
      }
    }

    object ExIsInstanceOf {
      def unapply(tree: TypeApply) : Option[(Tree, Tree)] = tree match {
        case TypeApply(Select(t, isInstanceOfName), typeTree :: Nil) if isInstanceOfName.toString == "isInstanceOf" => Some((typeTree, t))
        case _ => None
      }
    }

    object ExLiteralMap {
      def unapply(tree: Apply): Option[(Tree, Tree, Seq[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("scala", "Predef", "Map", "apply"), fromTypeTree :: toTypeTree :: Nil), args) =>
          Some((fromTypeTree, toTypeTree, args))
        case _ =>
          None
      }
    }
    object ExEmptyMap {
      def unapply(tree: TypeApply): Option[(Tree, Tree)] = tree match {
        case TypeApply(ExSelected("scala", "collection", "immutable", "Map", "empty"), fromTypeTree :: toTypeTree :: Nil) =>
          Some((fromTypeTree, toTypeTree))
        case TypeApply(ExSelected("scala", "Predef", "Map", "empty"), fromTypeTree :: toTypeTree :: Nil) =>
          Some((fromTypeTree, toTypeTree))
        case _ =>
          None
      }
    }

    object ExFiniteSet {
      def unapply(tree: Apply): Option[(Tree,List[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("Set", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case Apply(TypeApply(ExSelected("leon", "lang", "Set", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case _ => None
      }
    }

    object ExFiniteBag {
      def unapply(tree: Apply): Option[(Tree, List[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("Bag", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case Apply(TypeApply(ExSelected("leon", "lang", "Bag", "apply"), Seq(tpt)), args) =>
          Some(tpt, args)
        case _ => None
      }
    }

    object ExFiniteMap {
      def unapply(tree: Apply): Option[(Tree, Tree, List[Tree])] = tree match {
        case Apply(TypeApply(ExSelected("Map", "apply"), Seq(tptFrom, tptTo)), args) =>
          Some((tptFrom, tptTo, args))
        case Apply(TypeApply(ExSelected("leon", "lang", "Map", "apply"), Seq(tptFrom, tptTo)), args) =>
          Some((tptFrom, tptTo, args))
        case _ => None
      }
    }

    object ExParameterLessCall {
      def unapply(tree: Tree): Option[(Tree, Symbol, Seq[Tree])] = tree match {
        case s @ Select(t, _) =>
          Some((t, s.symbol, Nil))

        case TypeApply(s @ Select(t, _), tps) =>
          Some((t, s.symbol, tps))

        case TypeApply(i: Ident, tps) =>
          Some((i, i.symbol, tps))

        case _ =>
          None
      }
    }

    object ExCall {
      def unapply(tree: Tree): Option[(Tree, Symbol, Seq[Tree], Seq[Tree])] = tree match {
        // foo / foo[T]
        case ExParameterLessCall(t, s, tps) =>
          Some((t, s, tps, Nil))

        // foo(args)
        case Apply(i: Ident, args) =>
          Some((i, i.symbol, Nil, args))

        // foo(args1)(args2)
        case Apply(Apply(i: Ident, args1), args2) =>
          Some((i, i.symbol, Nil, args1 ++ args2))

        // foo[T](args)
        case Apply(ExParameterLessCall(t, s, tps), args) =>
          Some((t, s, tps, args))

        // foo[T](args1)(args2)
        case Apply(Apply(ExParameterLessCall(t, s, tps), args1), args2) =>
          Some((t, s, tps, args1 ++ args2))

        case _ => None
      }
    }

    object ExUpdate {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
              s @ Select(lhs, update),
              index :: newValue :: Nil) if s.symbol.fullName.endsWith("Array.update") =>
            Some((lhs, index, newValue))
        case _ => None
      }
    }

    object ExArrayFill {
      def unapply(tree: Apply): Option[(Tree, Tree, Tree)] = tree match {
        case Apply(
               Apply(
                 Apply(
                   TypeApply(ExSelected("scala", "Array", "fill"), baseType :: Nil),
                   length :: Nil
                 ),
                 defaultValue :: Nil
               ),
               manifest
             ) =>
            Some((baseType, length, defaultValue))
        case _ => None
      }
    }
  }
}
