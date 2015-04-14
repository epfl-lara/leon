/* Copyright 2009-2015 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Definitions._

object ScopingPhase extends UnitPhase[Program] {
  
  val name = "Scoping phase"
  val description = "Insert scoping information to all definitions in the program"
  
  def apply(ctx: LeonContext, p: Program) {
    insertScopingInformation(p, None)
  }

  private def insertScopingInformation(df : Definition , parent : Option[Definition]) {
    df.origOwner = parent
    for (sub <- df.subDefinitions){
      insertScopingInformation(sub, Some(df))
    }
  }
  
}