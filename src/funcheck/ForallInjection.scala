package funcheck


trait ForallInjection { self: AnalysisComponent =>
   import global._
   
   def mircoTraverser(unit: CompilationUnit)(tree: Tree): Unit = {
      lazy val genAnnot: Symbol = definitions.getClass("funcheck.lib.Specs.generator")

      tree match {
        case d @ DefDef(mods, name, _, _, _, _) => {
          /** Looking for contracts on the current method definition */
          mods.annotations.foreach((ann: Annotation) => {
            ann.constr match {
              /** Looks for the "signature" of the desired annotations */
              case Apply(Select(New(i:Select), _), Nil) => {
                i.symbol match {
                  case s if s == genAnnot => println("Found a generator annotation in: " + name.toString)
                  case _ => ;
                }
              }

              case _ => ;
            }
          })
        }
        case _ => ;
      }
    }
}
