Command Line Options
====================

Here is an overview of the command-line options that Leon recognizes: ::

  [  Info  ] Options that determine the feature of Leon to be used (mutually exclusive). Default: verify
  [  Info  ] --eval                Evaluate ground functions
  [  Info  ] --help                Show help message
  [  Info  ] --noop                No operation performed, just output program
  [  Info  ] --repair              Repair selected functions
  [  Info  ] --synthesis           Partial synthesis of choose() constructs
  [  Info  ] --termination         Check program termination
  [  Info  ] --verify              Verify function contracts
  [  Info  ] --xlang               Support for extra program constructs (imperative,...)
  [  Info  ] 
  [  Info  ] Additional top-level options
  [  Info  ] --debug=d1,d2,...     Enable detailed messages per component.
  [  Info  ]                       Available:
  [  Info  ]                         datagen
  [  Info  ]                         eval
  [  Info  ]                         leon
  [  Info  ]                         options
  [  Info  ]                         positions
  [  Info  ]                         repair
  [  Info  ]                         solver
  [  Info  ]                         synthesis
  [  Info  ]                         termination
  [  Info  ]                         timers
  [  Info  ]                         trees
  [  Info  ]                         verification
  [  Info  ]                         xlang
  [  Info  ] --functions=f1,f2,... Only consider functions f1, f2, ...
  [  Info  ] --solvers=s1,s2,...   Use solvers s1, s2,...
  [  Info  ]                       Available: 
  [  Info  ]                         enum           : Enumeration-based counter-example-finder
  [  Info  ]                         fairz3         : Native Z3 with z3-templates for unfolding (default)
  [  Info  ]                         smt-cvc4       : CVC4 through SMT-LIB
  [  Info  ]                         smt-cvc4-cex   : CVC4 through SMT-LIB, in-solver finite-model-finding, for counter-examples only
  [  Info  ]                         smt-cvc4-proof : CVC4 through SMT-LIB, in-solver inductive reasonning, for proofs only
  [  Info  ]                         smt-z3         : Z3 through SMT-LIB
  [  Info  ]                         smt-z3-q       : Z3 through SMT-LIB, with quantified encoding
  [  Info  ]                         unrollz3       : Native Z3 with leon-templates for unfolding
  [  Info  ] --strict              Terminate after each phase if there is an error
  [  Info  ] --timeout=t           Set a timeout for each verification/repair (in sec.)
  [  Info  ] 
  [  Info  ] Additional options, by component:
  [  Info  ] 
  [  Info  ] File output (Output parsed/generated program to the specified directory (default: leon.out))
  [  Info  ] --o=dir               Output directory
  [  Info  ] 
  [  Info  ] Scalac Extraction (Extraction of trees from the Scala Compiler)
  [  Info  ] --strictCompilation   Exit Leon after an error in compilation
  [  Info  ] 
  [  Info  ] Synthesis (Partial synthesis of "choose" constructs)
  [  Info  ] --cegis:opttimeout    Consider a time-out of CE-search as untrusted solution
  [  Info  ] --cegis:shrink        Shrink non-det programs when tests pruning works well
  [  Info  ] --cegis:vanuatoo      Generate inputs using new korat-style generator
  [  Info  ] --costmodel=cm        Use a specific cost model for this search
  [  Info  ] --derivtrees          Generate derivation trees
  [  Info  ] --manual=cmd          Manual search
  [  Info  ] 
  [  Info  ] Z3-f (Fair Z3 Solver)
  [  Info  ] --checkmodels         Double-check counter-examples with evaluator
  [  Info  ] --codegen             Use compiled evaluator instead of interpreter
  [  Info  ] --evalground          Use evaluator on functions applied to ground arguments
  [  Info  ] --feelinglucky        Use evaluator to find counter-examples early
  [  Info  ] --unrollcores         Use unsat-cores to drive unrolling while remaining fair
  [  Info  ] 
  [  Info  ] cvc4 solver (Solver invoked when --solvers=smt-cvc4)
  [  Info  ] --solver:cvc4=<cvc4-opt>Pass extra arguments to CVC4

