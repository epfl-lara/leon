package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

trait NameAnalyzer extends Extractors {
  self: AnalysisComponent =>

  import global._
  import StructuralExtractors._
  
  def collectNames(unit: CompilationUnit): Unit = {

  }
}
