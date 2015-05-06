Leon 3.0 [![Build Status](https://travis-ci.org/epfl-lara/leon.png?branch=master)](https://travis-ci.org/epfl-lara/leon)
==========

Getting Started
---------------

This section gives a very quick overview of how to build and use Leon; refer to
the following sections if you wish (or need) more detailed information.

To build it, you will need, the following:

* Java Runtime Environment, from Oracle, e.g. Version 7 Update 5 (to run sbt and scala)
* Scala, from Typesafe, e.g. version 2.11.5
* sbt, at least version 0.13.1 (to build Leon)
* a recent GLIBC3 or later, works with e.g. _apt-get_ (for Z3)
* GNU Multiprecision library, e.g. gmp3, works with e.g. _apt-get_ (for Z3)

The following can be obtained from the web, but for convenience they are contained in the
repository and are actually automatically handled by the default build configuration:

  * ScalaZ3 hosted on [GitHub](https://github.com/psuter/ScalaZ3/)
  * The [libz3 library](http://z3.codeplex.com/) from microsoft

To build, type this:

    $ sbt clean
    $ sbt package # takes a while
    $ sbt script

Then you can try e.g.

    $ ./leon ./testcases/verification/sas2011-testcases/RedBlackTree.scala

and get something like this:

<pre>
  ┌──────────────────────┐
╔═╡ Verification Summary ╞════════════════════════════════════════════════════════════════════════╗
║ └──────────────────────┘                                                                        ║
║ add                        postcondition                         82:15   valid    Z3-f    0.066 ║
║ add                        precond. (call ins(x, t))             81:15   valid    Z3-f    0.004 ║
║ add                        precond. (call makeBlack(ins(x, t)))  81:5    valid    Z3-f    0.021 ║
║ balance                    match exhaustiveness                  90:5    valid    Z3-f    0.006 ║
║ balance                    postcondition                         101:15  valid    Z3-f    0.068 ║
║ blackBalanced              match exhaustiveness                  45:43   valid    Z3-f    0.004 ║
║ blackHeight                match exhaustiveness                  50:40   valid    Z3-f    0.005 ║
║ buggyAdd                   postcondition                         87:15   invalid  Z3-f    2.080 ║
║ buggyAdd                   precond. (call ins(x, t))             86:5    invalid  Z3-f    0.027 ║
║ buggyBalance               match exhaustiveness                  104:5   invalid  Z3-f    0.007 ║
║ buggyBalance               postcondition                         115:15  invalid  Z3-f    0.042 ║
║ content                    match exhaustiveness                  17:37   valid    Z3-f    0.027 ║
║ ins                        match exhaustiveness                  59:5    valid    Z3-f    0.004 ║
║ ins                        postcondition                         66:15   valid    Z3-f    2.399 ║
║ ins                        precond. (call ins(x, t.left))        62:37   valid    Z3-f    0.013 ║
║ ins                        precond. (call ins(x, t.right))       64:40   valid    Z3-f    0.014 ║
║ makeBlack                  postcondition                         77:14   valid    Z3-f    0.015 ║
║ redDescHaveBlackChildren   match exhaustiveness                  40:53   valid    Z3-f    0.004 ║
║ redNodesHaveBlackChildren  match exhaustiveness                  34:54   valid    Z3-f    0.005 ║
║ size                       match exhaustiveness                  22:33   valid    Z3-f    0.004 ║
║ size                       postcondition                         25:15   valid    Z3-f    0.023 ║
╟┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄╢
║ total: 21     valid: 17     invalid: 4      unknown 0                                     4.838 ║
╚═════════════════════════════════════════════════════════════════════════════════════════════════╝
</pre>

Building Leon
-------------

Leon requires quite a few dependencies, and you will need to make sure
everything is correctly set up before being able to build it. Leon is probably
much easier to build on Unix-like plattforms. Not to say it is impossible to
build on Windows. But some scripts used to run and test the system are shell
script and you will need to manually port them to Windows if you wish to use
Windows.

First you need a Java Runtime Environment. The most recent version should work.
Simply follow the standard installation process (e.g. _apt-get_) for your system.

Next, you need the [Simple Build Tool](http://www.scala-sbt.org/) (sbt)
which seems to be (as of today) the standard way to build Scala program. Again
you should follow the installation procedure. You can also find information
about sbt [here](http://typesafe.com/platform/tools/scala/sbt). Sbt is quite a complex
tool, so I would suggest looking at the getting started guide on the wiki page.
However, if you just want to quickly build Leon and never look back, then the
information provided here should be sufficient.

(This section is outdated for linux, but can be useful to adapt on Windows/Mac)
Now you will have to build the [ScalaZ3 project](https://github.com/psuter/ScalaZ3/).
You should follow the instructions given in
the ScalaZ3 project. The ScalaZ3 is a Scala wrapper on the Z3 native library
from Microsoft. It is used in Leon to make native call to Z3. The generated
.jar from ScalaZ3 will be dependent on your own z3 native library, which you
can obtain from [here](http://z3.codeplex.com/).
However, the ScalaZ3 repository comes with 32 and 64 bits version for Linux and
you should probably use those ones to make sure the version is compatible. You
can install the Z3 native library in some standard system library path such as
_/usr/lib_. You need to install the _scalaz3.jar_ file in the "unmanaged"
directory. The build system is configured to use any jar file in the
"unmanaged" directory. Finally be aware that the Z3 library will come with its
own set of dependencies, in particular you will need to have GMP. You will
probably have to fight with a few errors before everything can finally work
together.

Finally you can build Leon. Start ```sbt``` from a terminal to get an interactive
sbt session. Then type:

    > clean
    
This will make sure the build is clean, then:

    > package
    
This will compile everything and create jar files. This could take a long time.
Finally you need to generate a running script with the command:

    > script
    
This will generate the leon script that can be used to run leon from command line
with correct arguments and classpath. This script you should not need to re-generate
another time, if you modify some code you just need to run ```compile``` again. If anything
goes wrong, you should carefully read the error message and try to fix it. You can
refer to the troubleshooting section of this manual.

Note that Leon is organised as a structure of two projects, with one main (or
root) project and one sub-project. From a user point of view, this should most
of the time be transparent and the build command should take care of
everything. The subproject is in _'library'_ and contains required code to make
Leon input programs valid Scala programs. The point of having this library
sub-project, is that you can use the generated jar for the library sub-project
on its own and you should be able to compile Leon testcases with the standard
Scala compiler.

Now we can make sure that the build went fine. Leon comes with a test suite.
Use ```sbt test``` to run all the tests.

Using Leon in Eclipse
---------------------

You first need to tell sbt to globally include the Eclipse plugin in its known plugins.
To do so type 

    $ echo "addSbtPlugin(\"com.typesafe.sbteclipse\" % \"sbteclipse-plugin\" % \"2.4.0\")" >> ~/.sbt/0.13/plugins/plugins.sbt

In your Leon home folder, type: ```sbt clean compile eclipse```

This should create all the necessary metadata to load Leon as a project in Eclipse.

You should now be able to [import the project](http://help.eclipse.org/juno/index.jsp?topic=%2Forg.eclipse.platform.doc.user%2Ftasks%2Ftasks-importproject.htm) into your Eclipse workspace. Don't forget to also import dependencies (the bonsai and scalaSmtlib projects, found somewhere in your ~/.sbt directory).

For each run configuration in Eclipse, you have to set the ECLIPSE_HOME environment variable to point to the home directory of your Eclipse installation. 
To do so, go to Run -> Run Configuration and then, after picking the configuration you want to run, set the variable in the Environment tab.

If you want to use ScalaTest from within Eclipse, download the ScalaTest plugin. For instructions, see [here](http://www.scalatest.org/user_guide/using_scalatest_with_eclipse). 
Do NOT declare your test packages as nested packages in separate lines, because ScalaTest will not see them for some reason. E.g. don't write 

<pre>
  package leon
  package test
  package myTestPackage 
</pre>

but instead

<pre>
  package leon.test.myTestPackage
</pre>

Changelog
---------

#### v?.?

* Add --watch option to automatically re-run Leon after file modifications.

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
