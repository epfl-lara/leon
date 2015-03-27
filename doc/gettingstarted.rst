Getting Started
===============

This section gives a very quick overview of how to build and start using Leon;
refer to the following :ref:`section <installation>` if you wish (or need) more
detailed information on how to setup Leon on your system.

To build Leon, you will need, the following:

* Java Runtime Environment, from Oracle, e.g. Version 7 Update 5 (to run sbt and scala)
* Scala, from Typesafe, e.g. version 2.11.5
* sbt, at least version 0.13.1 (to build Leon)
* a recent GLIBC3 or later, works with e.g. ``apt-get`` (for Z3)
* GNU Multiprecision library, e.g. gmp3, works with e.g. ``apt-get`` (for Z3)

The following can be obtained from the web, but for convenience they are
contained in the repository and are actually automatically handled by the
default build configuration:

* ScalaZ3 hosted on `GitHub <https://github.com/psuter/ScalaZ3/>`_
* The `libz3 library <http://z3.codeplex.com/>`_ from microsoft

To build, type this::

    $ sbt clean
    $ sbt package # takes a while
    $ sbt script

Then you can try e.g::

    $ ./leon ./testcases/verification/sas2011-testcases/RedBlackTree.scala

and get something like this::

    ┌──────────────────────┐
  ╔═╡ Verification Summary ╞═════════════════════════════════════════════════════════════════════╗
  ║ └──────────────────────┘                                                                     ║
  ║ add                            postcondition            83:22    valid        Z3-f     0.057 ║
  ║ add                            precondition             82:5     valid        Z3-f     0.017 ║
  ║ add                            precondition             82:15    valid        Z3-f     0.003 ║
  ║ balance                        match exhaustiveness     91:5     valid        Z3-f     0.005 ║
  ║ balance                        postcondition            102:22   valid        Z3-f     0.055 ║
  ║ blackBalanced                  match exhaustiveness     46:43    valid        Z3-f     0.003 ║
  ║ blackHeight                    match exhaustiveness     51:40    valid        Z3-f     0.004 ║
  ║ buggyAdd                       postcondition            88:22    invalid      Z3-f     1.162 ║
  ║ buggyAdd                       precondition             87:5     invalid      Z3-f     0.027 ║
  ║ buggyBalance                   match exhaustiveness     105:5    invalid      Z3-f     0.007 ║
  ║ buggyBalance                   postcondition            116:22   invalid      Z3-f     0.017 ║
  ║ content                        match exhaustiveness     18:37    valid        Z3-f     0.034 ║
  ║ ins                            match exhaustiveness     60:5     valid        Z3-f     0.003 ║
  ║ ins                            postcondition            67:22    valid        Z3-f     1.753 ║
  ║ ins                            precondition             63:37    valid        Z3-f     0.011 ║
  ║ ins                            precondition             65:40    valid        Z3-f     0.012 ║
  ║ makeBlack                      postcondition            78:21    valid        Z3-f     0.012 ║
  ║ redDescHaveBlackChildren       match exhaustiveness     41:53    valid        Z3-f     0.003 ║
  ║ redNodesHaveBlackChildren      match exhaustiveness     35:54    valid        Z3-f     0.004 ║
  ║ size                           match exhaustiveness     23:33    valid        Z3-f     0.004 ║
  ║ size                           postcondition            26:15    valid        Z3-f     0.043 ║
  ╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
  ║ total: 21     valid: 17     invalid: 4      unknown 0                                  3.236 ║
  ╚══════════════════════════════════════════════════════════════════════════════════════════════╝
