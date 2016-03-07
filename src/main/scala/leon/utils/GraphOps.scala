/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

object GraphOps {
  
  /**
   * Takes an graph in form of a map (vertex -> out neighbors).
   * Returns a topological sorting of the vertices (Right value) if there is one.
   * If there is none, it returns the set of vertices that belong to a cycle 
   * or come before a cycle (Left value)
   */
  def topologicalSorting[A](toPreds: Map[A,Set[A]]) : Either[Set[A], Seq[A]] = {
    def tSort(toPreds: Map[A, Set[A]], done: Seq[A]): Either[Set[A], Seq[A]] = {
      val (noPreds, hasPreds) = toPreds.partition { _._2.isEmpty }
      if (noPreds.isEmpty) {
        if (hasPreds.isEmpty) Right(done.reverse) 
        else Left(hasPreds.keySet)
      } 
      else {
        val found : Seq[A] = noPreds.keys.toSeq
        tSort(hasPreds mapValues { _ -- found }, found ++ done)    
      }
    }
    tSort(toPreds, Seq())
  }


  def transitiveClosure[A](graph: Map[A,Set[A]]) : Map[A,Set[A]] = {
    def step(graph : Map[A, Set[A]]) : Map[A,Set[A]] = graph map {
      case (k, vs) => (k, vs ++ (vs flatMap { v =>
        graph.getOrElse(v, Set())
      }))
    }
    fixpoint(step, -1)(graph)
  }
  
  def sources[A](graph : Map[A,Set[A]]) = {
    val notSources = graph.values.toSet.flatten
    graph.keySet -- notSources
  }
  
  def sinks[A](graph : Map[A,Set[A]]) = 
    graph.collect{ case (v, out) if out.isEmpty => v }.toSet
  /**
   * Returns the set of reachable nodes from a given node, 
   * not including the node itself (unless it is member of a cycle)
   * @param next A function giving the nodes directly accessible from a given node
   * @param source The source from which to begin the search
   */
  def reachable[A](next : A => Set[A], source : A) : Set[A] = {
    var seen = Set[A]()
    def rec(current : A) {
      val notSeen = next(current) -- seen
      seen ++= notSeen
      for (node <- notSeen) {
        rec(node)
      }
    }
    rec (source)
    seen
  }
  
  /**
   * Returns true if there is a path from source to target. 
   * @param next A function giving the nodes directly accessible from a given node
   */
  def isReachable[A](next : A => Set[A], source : A, target : A) : Boolean = {
    var seen : Set[A] = Set(source)
    def rec(current : A) : Boolean = {
      val notSeen = next(current) -- seen
      seen ++= notSeen
      (next(current) contains target) || (notSeen exists rec)
    }
    rec(source)
  } 
  
}
