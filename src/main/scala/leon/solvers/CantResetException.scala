package leon.solvers

class CantResetException(s: Solver) extends Exception(s"Unable to reset solver $s")
