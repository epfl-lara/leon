.. _library:

Leon Library
============

Leon defines its own versions of most data structures. One
of the reasons is to ensure that these operations can be
correctly mapped to mathematical functions and relations
inside of SMT solvers, largely defined by the SMT-LIB
standard (see http://www.smt-lib.org/).

To use Leon's libraries, you need to use the appropriate
`import` directive at the top of Leon's compilation units.
Here is a quick summary of what to import.

+--------------------------------+----------------------------------------------------+
| Package to import              | What it gives access to                            |
+================================+====================================================+
|`leon.annotation`               | Leon annotations, e.g. @induct                     |
+--------------------------------+----------------------------------------------------+
|`leon.lang`                     | `Map`, `Set`, `holds`, `passes`, `invariant`       |
+--------------------------------+----------------------------------------------------+
|`leon.collection.List`          | List[T]                                            +
+--------------------------------+----------------------------------------------------+
|`leon.collection.Option`        | Option[T]                                          +
+--------------------------------+----------------------------------------------------+
|`leon.lang.string`              | String                                             +
+--------------------------------+----------------------------------------------------+
|`leon.lang.xlang`               | epsilon                                            +
+--------------------------------+----------------------------------------------------+
|`leon.lang.synthesis`           | choose, ???, ?, ?!                                 +
+--------------------------------+----------------------------------------------------+

In the sequel we outline some of the libraries. To learn more, we encourage you to
look in the `library/` subdirectory of Leon distribution.

List
^^^^

Set
^^^

Option
^^^^^^

Map
^^^


