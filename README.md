Leon 3.0 [![Build Status](http://laraquad4.epfl.ch:9000/epfl-lara/leon/status/master)](http://laraquad4.epfl.ch:9000/epfl-lara/leon)
==========

Getting Started
---------------

To build Leon you will need JDK, scala, sbt, and some external solver binaries.
On Linux, it should already work out of the box.

To get started, see the documentation chapters, such as
  * [Getting Started](src/sphinx/gettingstarted.rst)
  * [Installation](src/sphinx/installation.rst)
  * [Introduction to Leon](src/sphinx/intro.rst)

[For change log, see CHANGELOG.md](CHANGELOG.md)

### The Stainless/Inox Stack

Leon verification has recently been split off into
  * [Inox](https://github.com/epfl-lara/inox) a backend solving layer, and
  * [Stainless](https://github.com/epfl-lara/stainless) a [Scala](http://scala-lang.org) frontend
    that supports contract-checking and termination proving.

Leon remains (for now) the main project for synthesis and repair as well as resource
bounds inference. However, developpment of verification-related features will most
likely be confined to the Stainless/Inox front.
