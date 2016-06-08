.. _installation:

Installing Leon
===============

Leon requires quite a few dependencies, and you will need to
make sure everything is correctly set up before being able
to build it. Leon is probably easiest to build on Linux-like
platforms, but read on regarding other platforms.

Due to its nature, this documentation section may not always
be up to date; we welcome pull requests with carefully
written and tested improvements to the information below.

**Requirements:**

* `Java SE Development Kit 8 <http://www.oracle.com/technetwork/java/javase/downloads/jdk8-downloads-2133151.html>`_ or `Java SE Development Kit 7 <http://www.oracle.com/technetwork/java/javase/downloads/jdk7-downloads-1880260.html>`_ for your platform
* SBT 0.13.x (Available from http://www.scala-sbt.org/)
* Support for at least one external solver (See :ref:`smt-solvers`)
* `Sphinx restructured text tool <http://sphinx-doc.org/>`_ (for building local documentation)

Linux & Mac OS-X
----------------

Get the sources of Leon by cloning the official Leon repository:

.. code-block:: bash

 $ git clone https://github.com/epfl-lara/leon.git
 Cloning into 'leon'...
 // ...
 $ cd leon
 $ sbt clean compile
 // takes about 3 minutes
 
We now use ``sbt script`` to create a ``leon`` bash script that runs Leon with
all the appropriate settings:

.. code-block:: bash
 
 $ sbt script
 $ ./leon --help

Note that Leon is organized as a structure of several
projects, with a main (or root) project and at least one
sub-project. From a user point of view, this should most of
the time be transparent and the build command should take
care of everything.

Windows
-------

Get the sources of Leon by cloning the official Leon
repository. You will need a Git shell for windows, e.g. 
`Git for Windows <https://git-for-windows.github.io/>`_.

.. code-block:: bash

 $ git clone https://github.com/epfl-lara/leon.git
 Cloning into 'leon'...
 // ...
 $ cd leon
 $ sbt clean compile
 // takes about 3 minutes
 
We now use ``sbt script`` to create a ``leon`` bash script that runs leon with
all the appropriate settings:

.. code-block:: bash
 
 $ sbt script

You will now need to either port the bash script to Windows, or to run it
under Cygwin.

**Known issues**

*Missing jars*

If running leon produces errors because it could not find
some cafebabe*.jar or vanuatoo*.jar, it is probably because
symlinks have not been resolved. If your architecture is
x64, do the following:

1. Copy ``unmanaged/common/cafebabe*.jar`` to ``unmanaged/64/``
2. Copy ``unmanaged/common/vanuatoo*.jar`` to ``unmanaged/64/``

You may be able to obtain additional tips on getting Leon to work on Windows 
from [Mikael Mayer](http://people.epfl.ch/mikael.mayer) or on [his dedicated web page](http://lara.epfl.ch/~mayer/leon/),

.. _smt-solvers:

External Solvers
----------------

Leon typically relies on external (SMT) solvers to solve the constraints it generates. 

We currently support two major SMT solvers:

  * CVC4, http://cvc4.cs.nyu.edu/web/
  * Z3, https://github.com/Z3Prover/z3

Solver binaries that you install should match your operating
system and your architecture.  We recommend that you install
these solvers as a binary and have their binaries available
in the ``$PATH``.  Once they are installed, you can instruct
Leon to use a given sequence of solvers.  The more solvers
you have installed, the more successful Leon might get,
because solver capabilities are incomparable.

In addition to these external binaries, a native Z3 API for
Linux is bundled with Leon and should work out of the box
(although having an external Z3 binary is a good idea in any
case). For other platforms you will have to recompile the
native Z3 communication layer yourself; see the section
below.

As of now the default solver is the native Z3 API, you will
have to explicitly specify another solver if this native
layer is not available to you, e.g., by giving the option
``--solvers=smt-cvc4`` to use CVC4. Check the ``--solvers``
option in :ref:`cmdlineoptions`.

In addition to SMT solvers, it is possible to automatically
invoke the Isabelle proof assistant on the proof obligations
that Leon generates. See :ref:`isabelle` for details.

Building ScalaZ3 and Z3 API
---------------------------

The main reason for using the Z3 API is that it is currently
faster when there are many calls to the solver, as in the
case of synthesis and repair.

To build the `ScalaZ3 <https://github.com/psuter/ScalaZ3/>`_ 
on Linux, you should follow the instructions given in the
ScalaZ3 project. The ScalaZ3 is a Scala wrapper on the Z3
native library from Microsoft. It is used in Leon to make
native call to Z3. The generated .jar from ScalaZ3 will be
dependent on your own z3 native library, which you can
obtain from http://z3.codeplex.com/ .  However, the
ScalaZ3 repository comes with 32 and 64 bits version for
Linux and you should probably use those ones to make sure
the version is compatible. You can install the Z3 native
library in some standard system library path such as
``/usr/lib``. You need to install the ``scalaz3.jar`` file in
the "unmanaged" directory. The build system is configured to
use any jar file in the "unmanaged" directory. Finally be
aware that the Z3 library will come with its own set of
dependencies, in particular you will need to have GMP. You
will probably have to fight with a few errors before
everything can finally work together.

An analogous process has been reported to be relatively
straightforward on OS-X and also possible on Windows.

Running Tests
-------------

Leon comes with a test suite. Consider running the following commands to
invoke different test suites:

 $ sbt test
 $ sbt integration:test
 $ sbt regression:test

Building Leon Documentation
---------------------------

To build this documentation locally, you will need Sphinx (
http://sphinx-doc.org/ ), a restructured text toolkit that
was originally developed to support Python documentation.

After installing sphinx, run ``sbt previewSite``. This will generate the documentation and open a browser.

The documentation resides in the ``src/sphinx/`` directory and can also be built without ``sbt``
using the provided ``Makefile``. To do this, in a Linux shell go to the directory ``src/sphinx/``,
type ``make html``, and open in your web browser the generated top-level local HTML file, by default stored in 
``src/sphinx/_build/html/index.html``. Also, you can open the ``*.rst`` documentation files in a text editor, since
they are human readable in their source form.

Using Leon in Eclipse
---------------------

You first need to tell sbt to globally include the Eclipse plugin in its known plugins.
To do so type 

.. code-block:: bash

 $ echo "addSbtPlugin(\"com.typesafe.sbteclipse\" % \"sbteclipse-plugin\" % \"2.4.0\")" >> ~/.sbt/0.13/plugins/plugins.sbt

In your Leon home folder, type: ```sbt clean compile eclipse```

This should create all the necessary metadata to load Leon as a project in Eclipse.

You should now be able to `import the project <http://help.eclipse.org/juno/index.jsp?topic=%2Forg.eclipse.platform.doc.user%2Ftasks%2Ftasks-importproject.htm>`_ into your Eclipse workspace. Don't forget to also import dependencies (the bonsai and scalaSmtlib projects, found somewhere in your ~/.sbt directory).

For each run configuration in Eclipse, you have to set the
``ECLIPSE_HOME`` environment variable to point to the home
directory of your Eclipse installation.  To do so, go to 

Run -> Run Configuration 

and then, after picking the configuration you want to run,
set the variable in the Environment tab.

If you want to use ScalaTest from within Eclipse, download the ScalaTest plugin. For instructions, 
see `Using ScalaTest with Eclise <http://www.scalatest.org/user_guide/using_scalatest_with_eclipse>`_. 
Do NOT declare your test packages as nested packages in
separate lines, because ScalaTest will not see them for some
reason. E.g. don't write

.. code-block:: scala

 package leon
 package test
 package myTestPackage 

but instead

.. code-block:: scala

 package leon.test.myTestPackage





Using Leon in IntelliJ
----------------------

You can maybe encounter some problems installing Leon, because of the various dependencies needed.
Here is a step-by-step guide having as a goal to help you to install your first Leon project and to be sure that every
dependency is present and correctly linked.

The advantage of using IntelliJ IDEA is that it provides a Scala plugin which allows you to directly import SBT project
into it.

**Installation:**

* `SBT 0.13.x <http://www.scala-sbt.org/>`_ (as described above)
* `IntelliJ IDEA <https://www.jetbrains.com/idea/download/>`_
* Leon project files, available in GitHub (as described above)
* Java SE Development Kit 8 or 7 (as described above)
* Support for at least one external solver (See :ref:`smt-solvers`)

**Setup STB in your project:**

Leon requires the Build class, which is a class created by SBT in its folder *target* when you compile your project the
first time. Also, it will be comfortable to run Leon through terminal command, in order to easily specify arguments.
We will resolve both of theses things running the command:

.. code-block:: bash

 $ sbt package script

This will create the *leon* executable file that you can now use typing ```./leon```. You are not required to recompile
this file after modifying your project, because *leon* file is actually a script that modifies the
scala compiler, giving it the path to Leon, and then compile the file you specified. You can open *leon*
in terminal ```cat leon``` to realize that.

**Setup IntelliJ:**

IntelliJ provides a Scala plugin. It will normally offer to install it by its own the first time you load a scala file,
anyway we suggest you install it manually before starting. Doing so will allow you to use sbt wizard import
in the next step.

In *Preferences -> Plugins* search for *Scala* and install it.

**Import Leon:**

Use the *New project from existing sources...* (*Import project* in welcome window) wizard of IntelliJ to import Leon.
Select the *SBT* external model and let
IntelliJ install it with the default options. Specify the Java SDK 1.8. When choosing the modules to import, only
select *Leon* and *Leon-build*
(maybe called *root* and *root-build*), we will import the other modules later manually.

You would now see only the *Leon* module in the IntelliJ project explorer. If you see *bonsai* or *smt-lib*, just
delete them.

**Setup dependencies:**

By right-clicking on Leon, choose *Open Module Setting*. Here you will set all the dependencies, in the so-named tab. If
SBT import tool worked well, you will see all needed dependencies present in your list and we will enable some of them.
Anyway, if some of them are not present (which happened to me), you can add it by your own clicking
``` "+" --> Add jar or folder --> ... ```. I will specify the path where you can find each dependency.

Enable:

* scala-smt-lib (can be found at ~/.sbt/0.13/staging/.../scala-smtlib/target/scala-2.11/classes)
* bonsai (can be found at ~/.sbt/0.13/stagging/.../bonsai/target/scala-2.11/classes)
* libisabel
* libisabel-setub
* scala-lang:... (enable all of them) (can be found at ~/.ivy2/cache/org.scala-lang/...)
* scalatest

If project has no SDK, add Java Library 1.8 (JDK 1.8)

The scala-lang:scala-library and scala-lang:scala-compiler must stand for the scala SDK provided by intelliJ, so
normally you haven't to add it. Anyway, if you encounter some problems, download it at with "+" -> Library -> Global Library
-> New Library and select the latest *Ivy* available. Ensure you have at least Scala 2.11 and NOT 2.10. Ensure also that
this added scala SDK is listed BELOW the scala-lang provided by SBT, so it has lower priority.

*.sbt* and *.ivy2* are folders created by SBT and are placed in your home folder.

If you find that some other modules are required to your project, feel free to add them but keep them below the ones
described in the priority list.

**Check your installation:**

*Make* the project in IntelliJ and try running it on some test files, like

.. code-block:: bash

 $ ./leon testcases/verification/datastructures/AssociativeList.scala
