.. _gettingstarted:

Getting Started
===============

This section gives a very quick overview of how to build and start using Leon;
refer to the following :ref:`installation` if you wish (or need) more
detailed information on how to setup Leon on your system.

To build Leon, you will need, the following:

* a 1.7 Java Development Kit, from Oracle (to run sbt and scala)
* sbt, at least version 0.13.X (to build Leon)

To build, type this

.. code-block:: bash

    $ sbt clean
    $ sbt compile # takes about 3 minutes
    $ sbt script

Then you can try e.g

.. code-block:: bash

    $ ./leon --solvers=smt-cvc4 ./testcases/verification/sas2011-testcases/RedBlackTree.scala

and get something like this

.. code-block:: bash

   ┌──────────────────────┐
 ╔═╡ Verification Summary ╞═══════════════════════════════════════════════════════════════════╗
 ║ └──────────────────────┘                                                                   ║
 ║ add                          postcondition          82:15   valid    U:smt-cvc4      0.258 ║
 ║ add                          precondition           81:15   valid    U:smt-cvc4      0.007 ║
 ║ add                          precondition           81:5    valid    U:smt-cvc4      0.049 ║
 ║ balance                      match exhaustiveness   90:5    valid    U:smt-cvc4      0.006 ║
 ║ balance                      postcondition          101:15  valid    U:smt-cvc4      0.301 ║
 ║ blackBalanced                match exhaustiveness   45:43   valid    U:smt-cvc4      0.006 ║
 ║ blackHeight                  match exhaustiveness   50:40   valid    U:smt-cvc4      0.009 ║
 ║ buggyAdd                     postcondition          87:15   invalid  U:smt-cvc4      1.561 ║
 ║ buggyAdd                     precondition           86:5    invalid  U:smt-cvc4      0.135 ║
 ║ buggyBalance                 match exhaustiveness   104:5   invalid  U:smt-cvc4      0.008 ║
 ║ buggyBalance                 postcondition          115:15  invalid  U:smt-cvc4      0.211 ║
 ║ content                      match exhaustiveness   17:37   valid    U:smt-cvc4      0.030 ║
 ║ ins                          match exhaustiveness   59:5    valid    U:smt-cvc4      0.007 ║
 ║ ins                          postcondition          66:15   valid    U:smt-cvc4      3.996 ║
 ║ ins                          precondition           62:37   valid    U:smt-cvc4      0.034 ║
 ║ ins                          precondition           64:40   valid    U:smt-cvc4      0.036 ║
 ║ makeBlack                    postcondition          77:14   valid    U:smt-cvc4      0.036 ║
 ║ redDescHaveBlackChildren     match exhaustiveness   40:53   valid    U:smt-cvc4      0.005 ║
 ║ redNodesHaveBlackChildren    match exhaustiveness   34:54   valid    U:smt-cvc4      0.007 ║
 ║ size                         match exhaustiveness   22:33   valid    U:smt-cvc4      0.005 ║
 ║ size                         postcondition          25:15   valid    U:smt-cvc4      0.055 ║
 ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
 ║ total: 21     valid: 17     invalid: 4      unknown 0                                6.762 ║
 ╚════════════════════════════════════════════════════════════════════════════════════════════╝

