.. _xlang:

XLang
=====

To complement the core PureScala language, the XLang module of Leon brings a
few extensions to that core language.

These extensions are kept as an optional feature, that needs to be explicitly
enabled from the command line with the option ``--xlang``. If you do not specify
the option, Leon will reject any program making use of an XLang feature.

Technically, these extensions are implemented using a translation to PureScala.
This means They are not implemented in the back-end solving system of Leon, but
parsed in the the front-end and eliminate early during the Leon pipelining
process.

Imperative Code
---------------

XLang lets you introduce local variables in functions, and use Scala assignments
syntax.

.. code-block:: scala

   def foo(x: Int): Int = {
     var a = x
     var b = 42
     a = a + b
     b = a
     b
   }

The above example illustrates three new features introduced by XLang:

1. Declaring a variable in a local scope

2. Blocks of statement

3. Assignment


While loops 

Arrays

Nested function closure on local variables.

.. note::
   some note comes here

Epsilon
-------


