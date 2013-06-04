package leon
package plugin

import scala.tools.nsc.{Global,Settings=>NSCSettings}

class ScalaCompiler(settings : NSCSettings, ctx: LeonContext) extends Global(settings, new SimpleReporter(settings, ctx.reporter)) {

  object leonExtraction extends {
    val global: ScalaCompiler.this.type = ScalaCompiler.this
    val runsAfter = List[String]("refchecks")
    val runsRightAfter = None
    val ctx = ScalaCompiler.this.ctx
  } with LeonExtraction

  override protected def computeInternalPhases() : Unit = {
    val phs = List(
      syntaxAnalyzer          -> "parse source into ASTs, perform simple desugaring",
      analyzer.namerFactory   -> "resolve names, attach symbols to named trees",
      analyzer.packageObjects -> "load package objects",
      analyzer.typerFactory   -> "the meat and potatoes: type the trees",
      patmat                  -> "translate match expressions",
      superAccessors          -> "add super accessors in traits and nested classes",
      extensionMethods        -> "add extension methods for inline classes",
      pickler                 -> "serialize symbol tables",
      refChecks               -> "reference/override checking, translate nested objects",
      leonExtraction          -> "extracts leon trees out of scala trees"
    )
    phs foreach { phasesSet += _._1 }
  }
}
