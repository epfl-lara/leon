.. _cmdlineoptions:

Command Line
============

Here is an overview of the command-line options that Leon recognizes: 

Choosing the feature to use
---------------------------

The first group of options determine which feature of Leon will be used. They are mutually exclusive,
with ``--verify`` being the default.

* ``--eval`` 
 
  Evaluates parameterless functions and value definitions.
  
* ``--verify``
  
  Proves or disproves function contracts, as explained in the :ref:`verification` section.

* ``--repair``
  
  Runs program :ref:`repair <repair>`.
  
* ``--synthesis``
  
  Partially synthesizes ``choose()`` constructs (see :ref:`synthesis` section).

* ``--termination``
  
  Runs a simple termination analysis.

* ``--xlang``
  
  Transforms a program written in the :ref:`xlang` language extension into a :ref:`purescala` program,
  then runs program verification.

* ``--noop``
  
  Runs the program through the extraction and preprocessing phases, then outputs it in the specified
  directory. Used mostly for debugging purposes.

* ``--help``
  
  Prints a helpful message, then exits.

Additional top-level options
----------------------------

These options are available by all Leon components:

* ``--debug=d1,d2,...``
  
  Enables printing detailed messages for the components d1,d2,... .
  Available components are: 

  * ``datagen`` (Data generators)
  
  * ``eval`` (Evaluators)
  
  * ``leon`` (The top-level component)
  
  * ``options`` (Prints parsed options)
  
  * ``repair`` (Program repair)
  
  * ``solver`` (SMT solvers)
  
  * ``synthesis`` (Program synthesis)
  
  * ``termination`` (Termination analysis)
  
  * ``timers`` (Timers, timer pools)
  
  * ``trees`` (Manipulation of trees)
  
  * ``verification`` (Verification)
  
  * ``xlang`` (Transformation of xlang into purescala programs)


* ``--functions=f1,f2,...``
  
  Only consider functions f1, f2, ... . This applies to all functionalities where Leon manipulates
  the input in a per-function basis.

* ``--solvers=s1,s2,...`` 
  
  Use solvers s1, s2,... . If more than one solver is chosen, all chosen solvers will be used in parallel,
  and the best result will be presented. By default, the ``fairz3`` solver is picked.
  Some solvers are specialized to proving verification conditions and will have hard time finding
  a counterexample in case of an invalid verification condition, some are specialized on finding
  counterexamples, and some provide a compromise between the two.

  Available solvers include:
  
  * ``enum`` 
    
    Uses enumeration-based techniques to discover counter-examples.
    This solver actually does not invoke an SMT solver and operates entirely on the level
    of Leon trees.

  * ``fairz3``

    Native Z3 with z3-templates for unfolding recursive functions (default).
  
  * ``smt-cvc4``
    
    CVC4 through SMT-LIB. An algorithm within Leon takes up the unfolding of recursive functions,
    lambdas etc. To use this and the following CVC4-based solvers, you will need to have the ``cvc4``
    executable in your system path (recommended is the latest unstable version).
  
  * ``smt-cvc4-cex``
 
    CVC4 through SMT-LIB, in-solver finite-model-finding, for counter-examples only.
  
  * ``smt-cvc4-proof``
   
    CVC4 through SMT-LIB, for proofs only. Inductive reasoning happens within the solver,
    through use of the SMTLIB-2.5 standard.
  
  * ``smt-z3``
   
    Z3 through SMT-LIB. To use this or the next solver, you will need to have the ``z3``
    executable in your program path (recommended: latest unstable version).
    Inductive reasoning happens on the Leon side (similarly to ``smt-cvc4``).
  
  * ``smt-z3-q``
   
    Z3 through SMT-LIB, but (recursive) functions are encoded with universal quantification,
    and inductive reasoning happens within the solver.
  
  * ``unrollz3``
    
    Native Z3, but inductive reasoning happens within Leon (similarly to ``smt-z3``).
  
* ``--strict``

  Terminate Leon after each phase if a non-fatal error is encountered 
  (such as a failed verification condition). By default, this option is activated.

* ``--timeout=t``

  Set a timeout for attempting to prove a verification condition/ repair a function (in sec.)
    
Additional Options, by Component:
---------------------------------

File Output
***********

* ``--o=dir``
  
  Output files to the directory ``dir`` (default: leon.out).
  Used when ``--noop`` is selected.

Code extraction
***************

* ``--strictCompilation``

  Do not try to recover after an error in compilation and exit Leon.

Synthesis
*********

* ``--cegis:opttimeout``

  Consider a time-out of CE-search as untrusted solution

* ``--cegis:shrink``

  Shrink non-det programs when tests pruning works well

* ``--cegis:vanuatoo``
 
  Generate inputs using new korat-style generator
  
* ``--costmodel=cm``
  
  Use a specific cost model for this search

* ``--derivtrees``
  
  Generate a derivation tree for every synthesized function.
  The trees will be output in ``*.dot`` files.

* ``--manual=cmd``
  
  Override Leon's automated search through the space of programs during synthesis.
  When this option is chosen, the user gets to traverse the space manually
  and choose how deductive synthesis rules are instantiated.

  The optional ``cmd`` argument is a series of natural numbers in the form ``n1,n1,...,nk``.
  It represents the series of command indexes that the search should instantiate at the 
  beginning of the search. Useful for repeated search attempts.

Fair-z3 Solver
**************
* ``--checkmodels``

  Double-check counter-examples with evaluator

* ``--codegen``
  
  Use compiled evaluator instead of interpreter

* ``--evalground``
 
  Use evaluator on functions applied to ground arguments
  
* ``--feelinglucky``
  
  Use evaluator to find counter-examples early

* ``--unrollcores``
 
  Use unsat-cores to drive unrolling while remaining fair
  
CVC4-solver
***********

* ``--solver:cvc4=<cvc4-opt>``
  
  Pass extra command-line arguments to CVC4.
