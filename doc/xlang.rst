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

2. Blocks of expressions

3. Assignment

You can use Scala variables with a few restrictions. The variables can only be
declared and used locally in the same function, and inner functions cannot
close over them. XLang introduces the possibility to use sequences of
expressions (blocks) -- a feature not available in PureScala, where you're only
option is a sequence of ``val`` which essentially introduce nested ``let``
declarations.

.. warning::
   Be careful when combining variables with nested functions from PureScala. Leon
   will reject code with nested functions accessing a variable from an outside scope:
   
   .. code-block::  scala

      def foo(x: Int) = {
        var a = 12
        def bar(y: Int): Int = {
          a = a + 1
          a + y
        }
        bar(17)
      }

   The problem with such code is the complications involved in representing closures as
   they need a pointer to an environment containing the variables. Leon is only able
   to handle closures with ``val``, where it is sufficient to explicitly pass the values
   as parameters.


While loops 
***********

Arrays
******


.. note::
   some note comes here

Epsilon
-------


