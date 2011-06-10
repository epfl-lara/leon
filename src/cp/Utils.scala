package cp

object Utils {

  private def indent(s : String) : String = s.split("\n").mkString("  ", "\n  ", "")

  object GenerateTerms {
    def apply(maxArity : Int) : String = {
      val termTraits = for (arity <- 1 to maxArity) yield {
        val traitArgParams = (1 to arity) map ("T" + _)
        val traitArgParamsString = traitArgParams.mkString(",")
        val traitParams = traitArgParams ++ Seq("R")
        val traitParamsString = traitParams.mkString("[", ",", "]")
        val termClassParamTuple = traitArgParams.mkString("(", ",", ")")
        val traitName = "Term%d%s" format (arity, traitParamsString)
        val booleanTraitName = "Term%d%s" format (arity, (traitArgParams ++ Seq("Boolean")).mkString("[", ",", "]"))
        val curriedImplicit2Boolean = "(implicit asBoolean : (R) => Boolean)"
        val curriedImplicit2Constraint = "(implicit asConstraint : t2c)"
        val anonFunParams = traitArgParams.zipWithIndex.map{ case (p, i) => "x_%d : %s" format (i, p) }
        val anonFunParamString = anonFunParams.mkString(",")
        val anonFunArgs = (0 until arity).map(i => "x_%d" format (i))
        val anonFunArgsString = anonFunArgs.mkString(",")
        val orMethod = """def ||(other : %s)%s : %s = 
  Term%d(this.program, Or(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (%s) => this.scalaFunction(%s) || other.scalaFunction(%s), this.types, this.converter)""" format (booleanTraitName, curriedImplicit2Boolean, booleanTraitName, arity, anonFunParamString, anonFunArgsString, anonFunArgsString)
        val andMethod = """def &&(other : %s)%s : %s = 
  Term%d(this.program, And(this.expr, other.expr), if (this.scalaFunction == null || other.scalaFunction == null) null else (%s) => this.scalaFunction(%s) && other.scalaFunction(%s), this.types, this.converter)""" format (booleanTraitName, curriedImplicit2Boolean, booleanTraitName, arity, anonFunParamString, anonFunArgsString, anonFunArgsString)
        val notMethod = """def unary_!%s : %s = 
  Term%d(this.program, Not(this.expr), if (this.scalaFunction == null) null else (%s) => ! this.scalaFunction(%s), this.types, this.converter)""" format (curriedImplicit2Boolean, booleanTraitName, arity, anonFunParamString, anonFunArgsString)
        
        val intTraitName = "Term%d%s" format (arity, (traitArgParams ++ Seq("Int")).mkString("[", ",", "]"))
        val minimizingMethod = 
"""def minimizing(minFunc : %s)%s : MinConstraint%d[%s] = {
  MinConstraint%d[%s](asConstraint(this), minFunc)
}""" format (intTraitName, curriedImplicit2Constraint, arity, traitArgParamsString, arity, traitArgParamsString)

        val composeMethods = (for (arityF <- 1 to (maxArity - arity + 1)) yield {
          for (index <- 0 until arity) yield {
            val fParams = (1 to arityF).map("A" + _)
            val thisParams = (1 to arity).map("T" + _)
            val fTermParams = fParams ++ Seq("T" + (index + 1))

            val resultParams = thisParams.take(index) ++ fParams ++ thisParams.drop(index + 1)
            val resultTermArity = arity + arityF - 1
            val resultTermParams = resultParams ++ Seq("R")

            val scalaFunctionParams = resultParams.zipWithIndex.map{ case (p, i) => "x_%d : %s" format (i, p) }
            val scalaFunctionArgs = (0 until resultParams.size).map("x_" + _)
            val fApplication = "other.scalaFunction(%s)" format (scalaFunctionArgs.drop(index).take(arityF).mkString(", "))
            val thisFunctionParams = scalaFunctionArgs.take(index) ++ Seq(fApplication) ++ scalaFunctionArgs.drop(index + arityF)
            val s2 =
"""def compose%d[%s](other : Term%d[%s]) : Term%d[%s] = {
  val (newExpr, newTypes) = Terms.compose(other, this, %d, %d, %d)
  Term%d(this.program, newExpr, if (this.scalaFunction == null || other.scalaFunction == null) null else (%s) => this.scalaFunction(%s), newTypes, this.converter)
}""" format (index, fParams.mkString(", "), arityF, fTermParams.mkString(", "), resultTermArity, resultTermParams.mkString(", "), index, arityF, arity, resultTermArity, scalaFunctionParams.mkString(", "), thisFunctionParams.mkString(", "))

            s2
          }
        }).flatten.mkString("\n\n")

        val (applyParams, applyArgs) = traitArgParams.zipWithIndex.map{ case (p, i) => ("x_%d : %s" format (i, p), "x_%d" format (i)) }.unzip

        val evaluatorArgs = traitArgParams.zipWithIndex.map{ case (p, i) => "converter.expr2scala(s(%d)).asInstanceOf[%s]" format (i, p) }
        val termTraitString =
"""trait %s extends Term[%s,%s] with Function%d[%s] {
  val convertingFunction = converterOf(this).exprSeq2scala%d[%s] _
  type t2c = (%s) => %s
  val scalaFunction : %s => %s
  lazy val evaluator : (Seq[Expr]) => R = (s : Seq[Expr]) => scalaFunction(%s)

  override def apply(%s) : R = scalaFunction(%s)

%s

%s

%s

%s

%s
}""" format (traitName, termClassParamTuple, "R", arity, traitParams.mkString(","), 
  arity, traitArgParamsString, 
  traitName, booleanTraitName, 
  termClassParamTuple, "R", 
  evaluatorArgs.mkString(","),
  applyParams.mkString(", "), applyArgs.mkString(", "), 
  indent(orMethod), indent(andMethod), indent(notMethod), indent(minimizingMethod), indent(composeMethods))
        
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
  def apply%s(conv : Converter, serializedProg : Serialized, serializedInputVars: Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Seq[Expr], scalaExpr : %s => %s) = {
    val (converter, program, expr, types) = Term.processArgs(conv, serializedProg, serializedInputVars, serializedOutputVars, serializedExpr, inputVarValues)
    new %s(program, expr, types, converter) with %s {
      val scalaFunction = scalaExpr
    }
  }
  
  def apply%s(program : Program, expr : Expr, scalaExpr : %s => %s, types : Seq[TypeTree], converter : Converter) =
    new %s(program, expr, types, converter) with %s {
      val scalaFunction = scalaExpr
    }
}""" format (arity, applyParamString, argParamTuple, "R", termClassName, termTraitName, applyParamString, argParamTuple, "R", termClassName, termTraitName)

        objectString
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
    val termTraits = GenerateTerms(args(0).toInt)
    val termObjects = GenerateTermObjects(args(0).toInt)
    val minConstraintsClasses = GenerateMinConstraintClasses(args(0).toInt)
    val typeAliases = GenerateTypeAliases(args(0).toInt)

    val converterMethods = GenerateConverterMethods(args(0).toInt)

    val everything = Seq(typeAliases, termTraits, termObjects, minConstraintsClasses).mkString("\n\n")
    println(indent(everything))
  }
}
