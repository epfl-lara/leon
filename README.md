Leon 2.2
==========

Getting Started
---------------

This section gives a very quick overview of how to build and use Leon; refer to
the following sections if you wish (or need) more detailed information.

To build it, you will need, the following:

* Java Runtime Environment, from Oracle, e.g. Version 7 Update 5 (to run sbt and scala)
* Scala, from Typesafe, e.g. version 2.10.3
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
    $ source ./setupenv

Then you can try e.g.

    $ ./leon ./testcases/sas2011-testcases/RedBlackTree.scala

and get something like this:

<pre>
    ┌─────────┐
  ╔═╡ Summary ╞═══════════════════════════════════════════════════════════════════════╗
  ║ └─────────┘                                                                       ║
  ║ add                       postcond.           valid               Z3-f+t    0.314 ║
  ║ add                       precond.    (82,14) valid               Z3-f+t    0.020 ║
  ║ add                       precond.    (82,18) valid               Z3-f+t    0.005 ║
  ║ balance                   postcond.           valid               Z3-f+t    0.409 ║
  ║ balance                   match.      (91,19) valid               Z3-f+t    0.034 ║
  ║ blackHeight               match.      (51,39) valid               Z3-f+t    0.004 ║
  ║ buggyAdd                  postcond.           invalid             Z3-f+t    4.084 ║
  ║ buggyAdd                  precond.     (87,8) invalid             Z3-f+t    0.111 ║
  ║ buggyBalance              postcond.           invalid             Z3-f+t    0.055 ║
  ║ buggyBalance              match.     (105,19) invalid             Z3-f+t    0.007 ║
  ║ ins                       postcond.           valid               Z3-f+t    6.577 ║
  ║ ins                       precond.    (63,40) valid               Z3-f+t    0.021 ║
  ║ ins                       precond.    (65,43) valid               Z3-f+t    0.005 ║
  ║ makeBlack                 postcond.           valid               Z3-f+t    0.007 ║
  ║ redNodesHaveBlackChildren match.      (35,56) valid               Z3-f+t    0.003 ║
  ║ size                      postcond.           valid               Z3-f+t    0.012 ║
  ╚═══════════════════════════════════════════════════════════════════════════════════╝
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

Type: ```sbt eclipse```

This should create all the necessary metadata for using Leon as a project in Eclipse.
Specifically, two Eclipse projects are generated in corresponding directories: the main *Leon* project in the Leon root directory, and the *Leon library* project in the ```library``` subdirectory.
You should now be able to [import the projects](http://help.eclipse.org/juno/index.jsp?topic=%2Forg.eclipse.platform.doc.user%2Ftasks%2Ftasks-importproject.htm) into your Eclipse workspace.
Since the main Leon project depends on the library, you should import both of them.


Changelog
---------

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
