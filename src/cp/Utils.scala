package cp

object Utils {

  /** Generate `compose' methods for terms */
  object GenerateCompose {
    private def indent(s : String) : String = s.split("\n").mkString("  ", "\n  ", "")

    def apply(maxArity : Int) : String = {
      val methods : Seq[String] = (for (arityG <- 1 to maxArity) yield {
        for (arityF <- 1 to (maxArity - arityG + 1)) yield {
          for (index <- 0 until arityG) yield {
            val sb = new scala.collection.mutable.StringBuilder
            sb.append("private def compose_")
            sb.append(index + "_" + arityF + "_" + arityG)
            val fParams = (1 to arityF).map("A" + _)
            val gParams = (1 to arityG).map("B" + _)

            val replacedGParams = gParams.take(index) ++ Seq("R1") ++ gParams.drop(index + 1)
            val allParams = fParams ++ Seq("R1") ++ (gParams.take(index) ++ gParams.drop(index + 1)) ++ Seq("R2")

            sb.append(allParams.mkString("[", ",", "]"))

            sb.append("(f : Term[")
            sb.append(fParams.mkString("(", ",", ")"))
            sb.append(",R1], g : Term[")
            sb.append(replacedGParams.mkString("(", ",", ")"))
            sb.append(",R2]) : Term")

            val newTermSize = arityG + arityF - 1
            val resultParams = gParams.take(index) ++ fParams ++ gParams.drop(index + 1) ++ Seq("R2")

            sb.append(resultParams.mkString(newTermSize + "[", ",", "]"))
            sb.append(" = {\n")
            sb.append(indent("val (newExpr, newTypes) = compose(f, g, " + index + ", " + arityF + ", " + arityG + ")"))
            sb.append("\n")
            sb.append(indent("Term" + newTermSize + "(f.program, newExpr, newTypes, f.converter)"))
            sb.append("\n")
            sb.append("}")
            sb.toString
          }
        }
      }).flatten.flatten

      methods.mkString("\n")
    }
  }
}
