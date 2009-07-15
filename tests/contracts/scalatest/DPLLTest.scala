//package scalatest.examples
//
//import org.scalatest.Suite
//
//
//
//class DPLLTest extends Suite {
//  import funpm.logic.DPLL._
//  
//  def testFindClausesWithOnlyOneLiteralAndReturnTheSingletonLiteralsForEachClause() {
//    expect(Set()) {
//      find_one_literals(Set())
//    }
//    expect(Set()) {
//      find_one_literals(Set(Set()))
//    }
//    expect(Set(pos("A"))) {
//      find_one_literals(Set(Set(pos("A"))))
//    }
//    expect(Set(pos("A"),neg("A"))) {
//      find_one_literals(Set(Set(pos("A")),Set(neg("A"))))
//    }
//    expect(Set()) {
//      find_one_literals(Set(Set(pos("A"),pos("B"))))
//    }
//  }
//	
//  
//  
//}
