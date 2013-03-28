package z3.scala

sealed abstract class Z3SearchFailure(val id: Int, val message: String)
case object Z3NoFailure extends Z3SearchFailure(0, "The last search was successful")
case object Z3Unknown extends Z3SearchFailure(1, "Undocumented failure reason")
case object Z3Timeout extends Z3SearchFailure(2, "Timeout")
case object Z3MemoutWatermark extends Z3SearchFailure(3, "Search hit a memory high-watermak limit")
case object Z3Canceled extends Z3SearchFailure(4, "External cancel flag was set")
case object Z3NumConflicts extends Z3SearchFailure(5, "Maximum number of conflicts was reached")
case object Z3IncompleteTheory extends Z3SearchFailure(6, "Theory is incomplete")
case object Z3Quantifiers extends Z3SearchFailure(7, "Logical context contains universal quantifiers")  


