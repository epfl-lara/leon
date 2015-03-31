Verification
============

Software verification aims at making software safer. In its typical use case,
it is a tool that takes as input the source code of a program with
specifications as annotations and attempt to prove --- or disprove --- their
validity.

One of the core module of Leon is a verifier for the subset of Scala described
in the sections :ref:`Pure Scala <purescala>` and :ref:`XLang <xlang>`. In this
section we describe the specification language that can be used to declare
properties of programs, as well as the safety properties automatically checked
by Leon. We also discuss how Leon can be used to prove mathematical theorems.

Verification conditions
-----------------------

Given an input program, Leon generates individual verification conditions
corresponding to different properties of the program. A program is correct if
all of the generated verification conditions are `valid`. The validity of some
conditions depends on the validity of other conditions --- typically a
postcondition is `valid` assuming the precondition is `valid`.

For each function, Leon attempts to verify its contract, if there is one. A
*contract* is the combination of a *precondition* and a *postcondition*. A
function meets its contract if for any input parameter that passes the
precondition, the postcondition holds after executing the function.
Preconditions and postconditions are annotations given by the user --- they are
the secifications and hence cannot be infered by a tool and must be provided.

In addition to user-provided contracts, Leon will also generate a few safety
verification conditions of its own. It will check that any array accesses are
within proper bounds, and that pattern matching always cover all possible cases,
even given complex precondition. The latter is different from the Scala compiler
check on pattern matching exhaustiveness, as Leon considers information provided
by (explicit or implicit) preconditions to the match expression.

Postconditions
**************


Preconditions
*************


Loop invariants
***************


Array access safety
*******************


Pattern matching exhaustiveness
*******************************



Proving mathematical theorems with Leon
---------------------------------------
