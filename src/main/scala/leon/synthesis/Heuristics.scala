/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.TypeTrees.TupleType

import heuristics._

object Heuristics {
  def all = List[Rule](
    IntInduction,
    InnerCaseSplit,
    //new OptimisticInjection(_),
    //new SelectiveInlining(_),
    //ADTLongInduction,
    ADTInduction
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name

}
