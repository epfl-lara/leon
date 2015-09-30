Change Log
----------

#### v?.?

Among the changes are (see the commits for details):
* Resource bound inference engine Orb, developed by Ravi is now merged into master
* Leon can now do program repair, thanks to Etienne and Manos
* Experimental support for first-order quantifiers inside Leon
* Isabelle proof assistant can now be used as a solver, thanks to Lars Hupel
* A DSL for writing equational proofs in Leon, thanks to Sandro Stucki and Marco Antognini
* Leon now uses the improved SMT-LIB library, thanks to the continuous work of Regis Blanc
* New case studies, including a little robot case study thanks to Etienne
* Improved termination checker of Nicolas Voirol with additions from Samuel Gruetter
* Many additions to Leon's library, including the state monad
* Numerous refactorings and bug fixes thanks to relentless work of Manos
* Add --watch option to automatically re-run Leon after file modifications, thanks to Etienne

#### v3.0
*Released 17.02.2015*

* Int is now treated as BitVector(32)
* Introduce BigInt for natural numbers

#### v2.4
*Released 10.02.2015*

* Implement support for higher-order functions

#### v2.3
*Released 03.03.2014*

* Accept multiple files with multiple modules/classes. Support class
  definitions with methods.
* Introduce the Leon library with common generic datastructures, List and
  Option for now.
* Add PortfolioSolver which tries a list of solvers (--solvers) in parallel.
* Add EnumerationSolver which uses Vanuatoo to guess models.
* Add documentation and sbt support for development under Eclipse,

#### v2.2
*Released 04.02.2014*

* Generics for functions and ADTs
* Use instantiation-time mixing for timeout sovlers
* Improve unrolling solvers to use incremental solvers

#### v2.1
*Released 10.01.2014*

* Reworked TreeOps API
* Tracing evaluators
* Support for range positions
* Support choose() in evaluators
* Flatten functions in results of synthesis
* Improved pretty printers with context information


#### v2.0

* First release
