//package contracts
//
//import org.scalacheck.{Arbitrary,Properties,Gen}
//import org.scalacheck.Prop._
//import org.scalacheck.ConsoleReporter.testStatsEx
//import org.scalacheck.Test.check
//import org.scalacheck.Arbitrary.arbitrary
//
//import java.util.{Arrays}
//
//
//
//object DPLLSpec /*extends Properties("DPLL")*/ {
//  import funpm.logic.DPLL._
//
//  
//   
//  //********************************************************//
//  // ARBITRARY GENERATORS
//  //********************************************************//
//  implicit val arbLiteral: Arbitrary[Literal] = Arbitrary(genLiteral)
//  implicit val arbClause: Arbitrary[List[Literal]] = Arbitrary(genClause)
//  implicit val arbClauseSet: Arbitrary[List[List[Literal]]] = Arbitrary {
//   for {
//     n <- Gen.choose(0,3)
//     s <- Gen.vectorOf(n,genClause)
//   } yield s
//  }
//  
//  
//  //********************************************************//
//  // GENERATORS
//  //********************************************************//
//    
//  // Literal (Data type)
//  def genLit(f: String => Literal) = for {
//    c <- Gen.choose(65,70) map (_.toChar)
//  } yield f(c.toString)  
//  
//  
//  def genPos = genLit(pos)
//  def genNeg = genLit(neg)
//  def genLiteral = Gen.frequency((2, genPos), (1, genNeg))
//  
//  
//  // List[Literal]
//  //XXX: Why doesn't this work with "Set" instead of "List"?!
//  def genClause = for {
//    n <- Gen.choose(0,3)
//    s <- Gen.vectorOf(n,genLiteral)
//  } yield s
//  
//  //********************************************************//
//  // UTILITARY METHOD
//  //********************************************************//
//  def listOfList2setOfSet[T](xss: List[List[T]]): Set[Set[T]] = 
//    Set() ++ (xss.map(xs => list2set(xs)))
//  
//  def list2set[T](xs: List[T]): Set[T] = 
//    Set() ++ xs
//  
//  def list2setOfSet[T](xs: List[T]): Set[Set[T]] = Set(list2set(xs))
//  
//  //********************************************************//
//  // PROPERTIES (To Test)
//  //********************************************************//
//   
//  
//  //********************************************************//
//  // find_one_literals
//  
//  val singleLiteral = property((lit: Literal) => find_one_literals(Set(Set(lit))) == Set(lit))
//  
//  val findLiteralInOneClause = property((clause: List[Literal]) => {
//    val clauseSet = list2setOfSet(clause)
//    val literals = find_one_literals(clauseSet)
//    clauseSet.filter(_.size == 1).:\[Set[Literal]](Set())((xss,xs) => xs ++ xss) == literals
//  })
//  
//  val findLiteralInClauseSet = property((clauses: List[List[Literal]]) => {
//    val clauseSet = listOfList2setOfSet(clauses)
//    val literals = find_one_literals(clauseSet)
//    
//    clauseSet.filter(_.size == 1).:\[Set[Literal]](Set())((xss,xs) => xs ++ xss) == literals
//  })
//  
//  //********************************************************//
//  // find_unique_literals
//  
//  val findUniqueLiteralsInClauseSet = property((clauses: List[List[Literal]]) => {
//    val clauseSet = listOfList2setOfSet(clauses)
//    val literals = find_unique_literals(clauseSet)
//    literals.forall(lit => clauseSet.forall(set => !set.contains(lit.flip)))
//  })
//  
//  
//  //********************************************************//
//  // one_literal_rule
////  val applyOneLiteralRule = property((clauses: List[List[Literal]], lit: Literal) => {
////    val clauseSet = listOfList2setOfSet(clauses)
////    
////  })
//  
//  val tests = List(
//    ("singleLiteral",  singleLiteral),
//    ("findLiteralInOneClause",  findLiteralInOneClause),
//    ("findLiteralInClauseSet", findLiteralInClauseSet),
//    ("findUniqueLiteralsInClauseSet", findUniqueLiteralsInClauseSet)
//  )
//  
//  
//  
//  
//  def main(args: scala.Array[String]) = 
//    tests foreach { case (name, p) => testStatsEx(name, check(p)) }
//
//}
