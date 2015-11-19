package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.TransformationPhase
import LazinessUtil._
import invariant.util.ProgramUtil._

/**
 * A class that maintains a data type that can be
 * used to create unique references
 */
/*class RefDataTypeManager(p: Program) {

  lazy val valueType = CaseClassType(CaseClassDef(FreshIdentifier("Unit"), Seq(), None, false), Seq())
  lazy val refStreamDef = {
    val cd = CaseClassDef(FreshIdentifier("Ref"), Seq(), None, false)
    cd.setFields(Seq(ValDef(FreshIdentifier("data", valueType)),
        ValDef(FreshIdentifier("next", valueType)))
  }
}*/
