package cp

object Utils {

  val composeMethods = scala.collection.mutable.Map[Int,Seq[String]]()
  private def indent(s : String) : String = s.split("\n").mkString("  ", "\n  ", "")

  /** Generate `compose' methods for terms */
  object GenerateCompose {
    def apply(maxArity : Int) : String = {
      val methods : Seq[String] = (for (arityG <- 1 to maxArity) yield {
        for (arityF <- 1 to (maxArity - arityG + 1)) yield {
          for (index <- 0 until arityG) yield {
            val methodName = "compose_%d_%d_%d" format (index, arityF, arityG)
            val fParams = (1 to arityF).map("A" + _)
            val gParams = (1 to arityG).map("B" + _)

            val replacedGParams = gParams.take(index) ++ Seq("R1") ++ gParams.drop(index + 1)
            val allParams = fParams ++ Seq("R1") ++ (gParams.take(index) ++ gParams.drop(index + 1)) ++ Seq("R2")

            val methodParams = allParams.mkString("[", ",", "]")

            val fParamsTuple = fParams.mkString("(", ",", ")")
            val replacedGParamsTuple = replacedGParams.mkString("(", ",", ")")

            val newTermSize = arityG + arityF - 1
            val resultParams = (gParams.take(index) ++ fParams ++ gParams.drop(index + 1) ++ Seq("R2")).mkString("[", ",", "]")

            val fParamsBrackets = fParams.mkString("[", ",", "]")
            val rangeType = "T" + (index + 1)
            val otherTypeParams = (fParams ++ Seq(rangeType)).mkString("[", ",", "]")
            val resultTermArity = arityG + arityF - 1
            val classParams = (1 to arityG) map ("T" + _)
            val resultTermParams = (classParams.take(index) ++ fParams ++ classParams.drop(index + 1) ++ Seq("R")).mkString("[", ",", "]")

            val s1 =
"""private def %s%s(f : Term[%s,%s], g : Term[%s,%s]) : Term%d%s = {
  val (newExpr, newTypes) = compose(f, g, %d, %d, %d)
  Term%d(f.program, newExpr, newTypes, f.converter)
}""" format (methodName, methodParams, fParamsTuple, "R1", replacedGParamsTuple, "R2", newTermSize, resultParams, index, arityF, arityG, newTermSize)

            val s2 =
"""def compose%d%s(other : Term%d%s) : Term%d%s = %s(other, this)""" format (index, fParamsBrackets, arityF, otherTypeParams, resultTermArity, resultTermParams, methodName)
            composeMethods(arityG) = s2 +: composeMethods.getOrElse(arityG,Nil)

            s1
          }
        }
      }).flatten.flatten
      val comments =
"""/********** TERM METHODS **********/
/** compose_i_j_k will compose f (of arity j) and g (of arity k) as "g∘f" by
 * inserting arguments of f in place of argument i of g */
"""
      comments + methods.mkString("\n\n")
    }
  }

  object GenerateTerms {
    def apply(maxArity : Int) : String = {
      val termTraits = for (arity <- 1 to maxArity) yield {
        val traitArgParams = (1 to arity) map ("T" + _)
        val traitArgParamsString = traitArgParams.mkString("[", ",", "]")
        val traitParams = traitArgParams ++ Seq("R")
        val traitParamsString = traitParams.mkString("[", ",", "]")
        val termClassParamTuple = traitArgParams.mkString("(", ",", ")")
        val traitName = "Term%d%s" format (arity, traitParamsString)
        val booleanTraitName = "Term%d%s" format (arity, (traitArgParams ++ Seq("Boolean")).mkString("[", ",", "]"))
        val orConstraintName = "OrConstraint%d%s" format (arity, traitArgParamsString)
        val andConstraintName = "AndConstraint%d%s" format (arity, traitArgParamsString)
        val notConstraintName = "NotConstraint%d%s" format (arity, traitArgParamsString)
        val curriedImplicit2Boolean = "(implicit asConstraint : t2c)"
        val orMethod = "def ||(other : %s)%s : %s = %s(this, other)" format (booleanTraitName, curriedImplicit2Boolean, booleanTraitName, orConstraintName)
        val andMethod = "def &&(other : %s)%s : %s = %s(this, other)" format (booleanTraitName, curriedImplicit2Boolean, booleanTraitName, andConstraintName)
        val notMethod = "def unary_!%s : %s = %s(this)" format (curriedImplicit2Boolean, booleanTraitName, notConstraintName)
        
        val intTraitName = "Term%d%s" format (arity, (traitArgParams ++ Seq("Int")).mkString("[", ",", "]"))
        val minimizingMethod = 
"""def minimizing(minFunc : %s)%s : MinConstraint%d%s = {
  MinConstraint%d%s(asConstraint(this), minFunc)
}""" format (intTraitName, curriedImplicit2Boolean, arity, traitArgParamsString, arity, traitArgParamsString)

        val composeMethodsString = composeMethods.getOrElse(arity, Nil).reverse.mkString("\n")

        val termTraitString =
"""sealed trait %s extends Term[%s,%s] {
  val convertingFunction = converterOf(this).exprSeq2scala%d%s _
  type t2c = (%s) => %s
  
%s

%s

%s

%s

%s
}""" format (traitName, termClassParamTuple, "R", arity, traitArgParamsString, traitName, booleanTraitName, indent(orMethod), indent(andMethod), indent(notMethod), indent(minimizingMethod), indent(composeMethodsString))
        
        termTraitString
      }

      termTraits.mkString("\n\n")
    }
  }

  object GenerateTermObjects {
    def apply(maxArity : Int) : String = {
      val objectStrings = for (arity <- 1 to maxArity) yield {
        val argParams = (1 to arity) map ("T" + _)
        val argParamsString = argParams.mkString("[", ",", "]")
        val applyParamString = (argParams ++ Seq("R")).mkString("[", ",", "]")
        val argParamTuple = argParams.mkString("(", ",", ")")
        val termClassName = "Term[%s,%s]" format (argParamTuple, "R")
        val booleanTermClassName = "Term[%s,%s]" format (argParamTuple, "Boolean")
        val termTraitName = "Term%d%s" format (arity, applyParamString)
        val booleanTermTraitName = "Term%d%s" format (arity, (argParams ++ Seq("Boolean")).mkString("[", ",", "]"))
        val objectString =
"""object Term%d {
  def apply%s(conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr]) = {
    val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
    new %s(program, expr, types, converter) with %s
  }
  
  def apply%s(program : Program, expr : Expr, types : Seq[TypeTree], converter : Converter) =
    new %s(program, expr, types, converter) with %s
}""" format (arity, applyParamString, termClassName, termTraitName, applyParamString, termClassName, termTraitName)

        val binaryOpObjectString =
"""object %sConstraint%d {
  def apply%s(l : %s, r : %s) : %s = (l, r) match {
    case (Term(p1,ex1,ts1,conv1), Term(p2,ex2,ts2,conv2)) => Term%d(p1,%s(ex1,ex2),ts1,conv1)
  }
}""" 
        val orObjectString = binaryOpObjectString format ("Or", arity, argParamsString, booleanTermClassName, booleanTermClassName, booleanTermTraitName, arity, "Or")
        val andObjectString = binaryOpObjectString format ("And", arity, argParamsString, booleanTermClassName, booleanTermClassName, booleanTermTraitName, arity, "And")

        val unaryOpObjectString =
"""object %sConstraint%d {
  def apply%s(c : %s) : %s = c match {
    case Term(p,ex,ts,conv) => Term%d(p,%s(ex),ts,conv)
  }
}"""

        val notObjectString = unaryOpObjectString format ("Not", arity, argParamsString, booleanTermClassName, booleanTermTraitName, arity, "Not")

        List(objectString, orObjectString, andObjectString, notObjectString).mkString("\n\n")
      }

      objectStrings.mkString("\n\n")
    }
  }

  object GenerateMinConstraintClasses {
    def apply(maxArity : Int) : String = {
      val classes = for (arity <- 1 to maxArity) yield {
        val params = (1 to arity) map ("T" + _)
        val paramString = params.mkString("[", ",", "]")
        val paramTupleString = params.mkString("(", ",", ")")
        val booleanTermParams = (params ++ Seq("Boolean")).mkString("[", ",", "]")
        val intTermParams = (params ++ Seq("Int")).mkString("[", ",", "]")
        val booleanTermName = "Term%d%s" format (arity, booleanTermParams)
        val intTermName = "Term%d%s" format (arity, intTermParams)
        val classString =
"""case class MinConstraint%d%s(cons : %s, minFunc : %s) extends MinConstraint[%s](cons, minFunc) {
  val convertingFunction = converterOf(cons).exprSeq2scala%d%s _
}""" format (arity, paramString, booleanTermName, intTermName, paramTupleString, arity, paramString)

        classString
      }

      classes.mkString("\n\n")
    }
  }

  object GenerateTypeAliases {
    def apply(maxArity : Int) : String = {
      var booleanTerms = List[String]()
      var intTerms = List[String]()

      booleanTerms = "type Constraint[T] = Term[T,Boolean]" :: booleanTerms
      intTerms = "type IntTerm[T] = Term[T,Int]" :: intTerms

      for (arity <- 1 to maxArity) {
        val params = (1 to arity) map ("T" + _)
        val paramWithBooleanString = (params ++ Seq("Boolean")).mkString("[", ",", "]")
        val paramWithIntString = (params ++ Seq("Int")).mkString("[", ",", "]")
        val paramString = params.mkString("[", ",", "]")
        val boolType = "type Constraint%d%s = Term%d%s" format (arity, paramString, arity, paramWithBooleanString)
        val intType = "type IntTerm%d%s = Term%d%s" format (arity, paramString, arity, paramWithIntString)

        booleanTerms = boolType :: booleanTerms
        intTerms = intType :: intTerms
      }

      val comment = """/** Type aliases for terms with boolean and integer range */"""
      (Seq(comment) ++ booleanTerms.reverse ++ intTerms.reverse).mkString("\n")
    }
  }

  object GenerateConverterMethods {
    def apply(maxArity : Int) : String = {
      val methods = for (arity <- 1 to maxArity) yield {
        val params = (1 to arity) map ("T" + _)
        val paramsBrackets = params.mkString("[", ",", "]")
        val paramsParen    = params.mkString("(", ",", ")")
        val tuple = params.zipWithIndex.map{ case (p, i) => "expr2scala(exprs(%d)).asInstanceOf[%s]" format (i, p) }.mkString("(", ",", ")")
        val methodString =
"""def exprSeq2scala%d%s(exprs : Seq[Expr]) : %s =
  %s""" format (arity, paramsBrackets, paramsParen, tuple)

        methodString
      }

      methods.mkString("\n\n")
    }
  }

  def main(args: Array[String]) : Unit = {
    val staticComposeMethods = GenerateCompose(args(0).toInt)
    val termTraits = GenerateTerms(args(0).toInt)
    val termObjects = GenerateTermObjects(args(0).toInt)
    val minConstraintsClasses = GenerateMinConstraintClasses(args(0).toInt)
    val typeAliases = GenerateTypeAliases(args(0).toInt)

    val converterMethods = GenerateConverterMethods(args(0).toInt)

    val everything = Seq(typeAliases, termTraits, termObjects, minConstraintsClasses, staticComposeMethods).mkString("\n\n")
    println(indent(everything))
  }
}
