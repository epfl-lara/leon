This is Leon 0.2.0

===============
Getting Started
===============

This section gives a very quick overview of how to build and use Leon, refer to
the following sections if you wish (or need) more detailed information.

To build it, you will need, for example, the following:
  * Java Runtime Environment, from Oracle, e.g. Version 7 Update 5 
    (to run xsbt and scala)
  * Scala, from Typesafe, e.g. version 2.9.1
  * xsbt, e.g. version 0.11.3: download sbt-launch.jar, run it with java -jar
    (to built Leon)
  * a recent GLIBC3 or later, works with e.g. apt-get
    (for Z3)
  * GNU Multiprecision library, e.g. gmp3, works with e.g. apt-get
    (for Z3)
The followin can be obtained from the web, but for convenience they are contained in the
repository and are actually automatically handled by the default build configuration.
  * ScalaZ3 from https://github.com/psuter/ScalaZ3/
  * The libz3 library from microsoft:
    http://research.microsoft.com/en-us/um/redmond/projects/z3/

To build, type this:

    $ xsbt clean
    $ xsbt package # takes a while
    $ xsbt script
    $ source ./setupenv

Then you can try e.g.

    $ ./leon ./testcases/sas2011-testcases/RedBlackTree.scala

and get something like this:

[ Info  ] . ┌─────────┐
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
          

=============
Building Leon
=============

Leon requires quite a few dependencies, and you will need to make sure
everything is correctly set up before being able to build it. Leon is probably
much easier to build on Unix-like plattforms. Not to say it is impossible to
build on Windows. But some scripts used to run and test the system are shell
script and you will need to manually port them to Windows if you wish to use
Windows.

First you need a Java Runtime Environment. The most recent version should work.
Simply follow the standard installation process (e.g. apt-get) for your system.

Next, you need the Simple Build Tool (sbt) https://github.com/harrah/xsbt/wiki
which seems to be (as of today) the standard way to build Scala program. Again
you should follow the installation procedure. You can also find information
about sbt here: http://typesafe.com/technology/sbt. Sbt is quite a complex
tool, so I would suggest looking at the getting started guide on the wiki page.
However, if you just want to quickly build Leon and never look back, then the
information provided here should be sufficient.

(This section is outdated for linux, but can be useful to adapt on Windows/Mac)
Now you will have to build the ScalaZ3 project from
https://github.com/psuter/ScalaZ3/. You should follow the instructions given in
the ScalaZ3 project. The ScalaZ3 is a Scala wrapper on the Z3 native library
from Microsoft. It is used in Leon to make native call to Z3. The generated
.jar from ScalaZ3 will be dependent on your own z3 native library, which you
can obtain from http://research.microsoft.com/en-us/um/redmond/projects/z3/.
However, the ScalaZ3 repository comes with 32 and 64 bits version for Linux and
you should probably use those ones to make sure the version is compatible. You
can install the Z3 native library in some standard system library path such as
/usr/lib. You need to install the scalaz3.jar file in the "unmanaged"
directory. The build system is configured to use any jar file in the
"unmanaged" directory. Finally be aware that the Z3 library will come with its
own set of dependencies, in particular you will need to have GMP. You will
probably have to fight with a few errors before everything can finally work
together.

Finally you can build Leon. Start sbt from a terminal to get an interactive
sbt session. Then type:
  clean
This will make sure the build is clean, then:
  package
This will compile everything and create jar files. This could take a long time.
Finally you need to generate a running script with the command:
  script
This will generate the leon script that can be used to run leon from command line
with correct arguments and classpath. This script you should not need to re-generate
another time, if you modify some code you just need to run 'compile' again. If anything
goes wrong, you should carefully read the error message and try to fix it. You can
refer to the troubleshooting section of this manual.

Note that Leon is organised as a structure of two projects, with one main (or
root) project and one sub-project. From a user point of view, this should most
of the time be transparent and the build command should take care of
everything. The subproject is in 'library' and contains required code to make
Leon input programs valid Scala programs. The point of having this library
sub-project, is that you can use the generated jar for the library sub-project
on its own and you should be able to compile Leon testcases with the standard
Scala compiler.

Now we can make sure that the build went fine. There is a collection of
testcase in 'regression' that are used to check the correctness of the system.
We provide a shell script 'run-tests.sh' to run all of them and make sure Leon
behaves as expected. You should run ./run-tests now to make sure everything is in
order. Note that running all tests can take some time.

==========
Using Leon
==========


========================
Layout of this directory
========================

Here is a quick overview of the conventions used in the layout of this directory.

  -src
    Contains all Scala sources for the Leon project. The layout of the sources follows the standard SBT (and Maven) convention.

  -regression
    Contains many small testcases. They are meant to be run automatically with a test script and Leon should behave correctly on
    all of them (correctly could mean either proving validity, finding counter-example or refusing the input).

  -testcases
    Contains somewhat realistic testcases, that correspond to existing algorithms. Leon might not successfully handle all of them.

  -README
    This file.

  -PERMISSION
    You can safely ignore this file.
    It is used to handle git PERMISSION for this repository.

  -build.sbt
  -project/Build.sbt
    Configuration of SBT.

  -library
    Sub-project containing the Leon library. Needed if one wishes to run Leon testcases with standard Scala.

  -unmanaged
    This is the directory used by the build system to find unmanated dependencies. You usually need to manually
    add files to this directory.

  -lib-bin
  -lib64-bin
    Contains some binary dependencies for the system that have been build for different plattform/OS.

  
===============
Troubleshooting 
===============

Sorry, not done yet :(
