/**
 * DPLL in Scala implemented by Hossein. This program has been suggested by Viktor 
 * because it uses Set and Map. Though, in order to fit in our purely functional 
 * Scala subset we will have to rework it a little bit.
 * 
 * [TODO] Make this program to fit in our purely functional Scala subset.
 */

package funpm.logic

import scala.collection.immutable.ListSet


object DPLL {
  type Clause = Set[Literal]
  type ClauseSet = Set[Clause]
  
  sealed abstract class Literal() {
    def flip: Literal    
  }
  case class pos(v : String) extends Literal {
    override def flip = neg(v)  
  }
  case class neg(v: String) extends Literal {
    override def flip = pos(v)
  }

  

  def negation(l: Literal) = l.flip
  
  /**
   * Finds the unit literals in a formula
   */
  def find_one_literals( cs : ClauseSet) : Clause = 
    new ListSet() ++ (cs.flatMap(c => if( c.size == 1) List(c.toArray(0)) else Nil)).elements
   
  
  
  /**
   * Apply the one-literal rule on a literal ``l''
   */
  def one_literal_rule( c : ClauseSet, l : Literal) : ClauseSet =
  { 
    var result = Set.empty[Clause]
    c.foreach(
         clause => if( clause.contains( negation(l))) result = result + (clause - negation(l))
                   else {if( !clause.contains(l)) result = result + clause}
       )
    result
  }
  /**
   * Repeatedly apply the one-literal rule
   * Returns the resulted clause set and the variable assignment
   */
  def repeat_one_literal( c : ClauseSet) : (ClauseSet,Map[String,Boolean]) =
  {
    val one_literals = find_one_literals( c)
    var result_clauseset = c
    var result_assignment = Map.empty[String,Boolean]
    for( l <- one_literals)
    {
      result_clauseset = one_literal_rule( result_clauseset, l)
      l match
      {
        case neg( v) => result_assignment = result_assignment + ( v -> false)
        case pos( v) => result_assignment = result_assignment + ( v -> true)  
      } 
    }
    (result_clauseset,result_assignment)
  }
  /**
   * Find the literal which occur only positively or negatively in a Clause set
   */
  def find_unique_literals( c : ClauseSet) : Clause =
  {
    var unique_literals = Set.empty[Literal]
    c.foreach( clause => unique_literals = unique_literals ++ clause)  
    unique_literals.foreach( l => if( unique_literals.contains( negation( l))) 
      {
        unique_literals = unique_literals - l
        unique_literals = unique_literals - negation(l)
      })    
    unique_literals    
  }
  
  /**
   * Apply the affirmative-negative rule on a literal ``l''
   */
  def affirmative_negative_rule( c : ClauseSet, l : Literal) : ClauseSet =
  {
    var result = c
    c.foreach( clause => if( clause.contains(l)) result = result - clause)    
    result  
  }
  /**
   * Repeatedly apply the affirmative-negative rule
   * Returns the resulted clause set and the variable assignment
   */
  def repeat_affirmative_negative( c : ClauseSet) : (ClauseSet,Map[String,Boolean]) = 
  {
    val unique_literals = find_unique_literals( c)
    var result_clauseset = c
    var result_assignment = Map.empty[String,Boolean]
    for( l <- unique_literals)
    {
      result_clauseset = affirmative_negative_rule( result_clauseset, l)
      l match
      {
        case neg( v) => result_assignment = result_assignment + ( v -> false)
        case pos( v) => result_assignment = result_assignment + ( v -> true)  
      }
    }
    (result_clauseset,result_assignment)
  }
  
  /**
   * Determines whether a clause set is satisfiable
   * Computes the assignment to the variables
   */
  def dpll( c : ClauseSet) : (Boolean,Map[String,Boolean]) =
  {
    var assignment = Map.empty[String,Boolean]
    // 1 - one-literal rule
    var current_clauseset = repeat_one_literal(c)
    assignment = current_clauseset._2
    if( current_clauseset._1.exists( clause => clause.isEmpty)) return (false,assignment)
    else if( current_clauseset._1.isEmpty) return (true,assignment)
    // 2 - affirmative-negative rule
    current_clauseset = repeat_affirmative_negative( current_clauseset._1)
    assignment = assignment ++ current_clauseset._2
    if( current_clauseset._1.exists( clause => clause.isEmpty)) return (false,assignment)
    else if( current_clauseset._1.isEmpty) return (true,assignment)
    // 3- splitting rule
    val first_clause = current_clauseset._1.toArray.first
    val literal_to_split = first_clause.toArray.first
    val split_left = dpll(current_clauseset._1 + Set(negation(literal_to_split)) )
    if( split_left._1) return ( true, split_left._2 ++ assignment)
    val split_right = dpll(current_clauseset._1 + Set(literal_to_split)) 
    return ( split_right._1, split_right._2 ++ assignment)
  }
    
    
  def main(args : Array[String]) : Unit = 
  {
    val form : ClauseSet = Set(  Set(neg("A"),neg("B"),pos("C")) , Set(pos("A"),pos("C"),pos("D")) , 
                                  Set(pos("A"),pos("C"),neg("D")) , Set(pos("A"),neg("C"),pos("D")) ,
                                  Set(pos("A"),neg("C"),neg("D")) , Set(neg("B"),neg("C"),pos("D")) ,
                                  Set(neg("A"),pos("B"),neg("C")) , Set(neg("A"),neg("B"),pos("C")))
    val res =  dpll( form)
    
    assert(res == (true,Map("B" -> true, "C" -> true, "A" -> true, "D" -> true)))

  }
}
