package leon
package purescala
package DataStructures 

class DirectedGraph[T] {
  
  var adjlist = scala.collection.mutable.Map[T, Set[T]]()
  
  def addEdge(src: T, dest: T): Unit = {
    val newset = if (adjlist.contains(src)) adjlist(src) + dest
    else Set(dest)

    //this has some side-effects 
    adjlist.update(src, newset)
  }

  def BFSReach(src: T, dest: T): Boolean = {
    var queue = List[T]()
    var visited = Set[T]()
    visited += src

    //TODO: is there a better (and efficient) way to implement BFS without using side-effects
    def BFSReachRecur(cur: T): Boolean = {
      var found: Boolean = false
      if (adjlist.contains(cur)) {
        adjlist(cur).foreach((fi) => {
          if (fi == dest) found = true
          else if (!visited.contains(fi)) {
            visited += fi
            queue ::= fi
          }
        })
      }
      if (found) true
      else if (queue.isEmpty) false
      else {
        val (head :: tail) = queue
        queue = tail
        BFSReachRecur(head)
      }
    }

    BFSReachRecur(src)
  }

  def containsEdge(src: T, dest: T) : Boolean = {
    if(adjlist.contains(src)) {
        adjlist(src).contains(dest)
    }
    else false
  }
  
  /*def Edges : Iterable[(T,T)] ={
    adjlist.foldLeft(Seq[(T,T)]())((acc,entry) => { 
      acc ++ entry._2.map((entry._1,_))
    })
  }*/
}

class UndirectedGraph[T] extends DirectedGraph[T] {
  
  override def addEdge(src: T, dest: T): Unit = {
    val newset1 = if (adjlist.contains(src)) adjlist(src) + dest
    else Set(dest)
    
    val newset2 = if (adjlist.contains(dest)) adjlist(dest) + src
    else Set(src)

    //this has some side-effects 
    adjlist.update(src, newset1)
    adjlist.update(dest, newset2)
  }  
  
  //consider only one pair for each undirected edge
  /*override def Edges : Iterable[(T,T)] ={   
    val edgeSet = adjlist.foldLeft(Set[(T,T)]())((acc,entry) => {       
      acc ++ entry._2.map((entry._1,_)).filter((edge) => !acc.contains((edge._2,edge._1)))
    })    
    edgeSet
  }*/ 
}
