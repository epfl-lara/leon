# Leon Coding Guidelines


Here are a few coding guidelines that should be followed when introducing new
code into Leon. Existing code that do not meet these guidelines should
eventually be fixed.

## Development

#### Global state must be concurrent-friendly

Leon relies on global state at several places, it should be assumed that this
global state can be accessed concurrently, it is thus necessary to ensure that
it will behave consistently. Global state should be ```private[this]``` and
accessor functions **synchronized**. Another possibility for things like
counters is to rely on Java classes such as ```AtomicInteger```.

Even though most of Leon is sequential, parts of it is concurrent (Portfolio
Solvers, Web interface, Interrupt threads, ...). It is likely to become more
concurrent in the future.

#### Code should be predictable

Leon's execution should be predictable and reproducible. Due to the complex
nature of its inner-working, it is crucial that problematic executions and bug
reports are consistently reproducible.

One of the main reason behind this unpredictability is the traversal of
structures that are not explicitly ordered(e.g. ``Set``, ``Map``, ..). Please
avoid that by either explicitly ordering after ``.toSeq``, or by using
different datastructures.


## Documentation

There are two levels of documentation in Leon. the subdirectory ```/doc```
contains a user manual intended for end-user of Leon. This documentation
describes the Leon language and the conceptual algorithms of Leon. It is
intended for people that wish to use Leon as a tool to help them write better
software. On the other hand, ScalaDoc is used in the source code of Leon for
describing the internal structure of Leon.

Ideally, all modules/classes that export some functionalities for other
modules/classes in Leon (or more broadly) should be documented using the
ScalaDoc.  We follow convention outlined
[here](http://docs.scala-lang.org/style/scaladoc.html).  Existing code is not
well documentated, but we should strive at improving that whenever we get the
opportunity.


## Testing

Leon tests are currently separated in three layers:
- unit tests
- integration tests
- regression tests

```sbt test``` runs only unit tests. Please do not push changes without testing them with ```sbt test integration:test```.


### Unit Tests

Leon should have unit-tests for commonly used functions. Although it is
convenient to rely on a program extracted from Scalac, it is NOT ok to
write a unit test that rely on an external system (e.g. scalac).
A unit test should be fast, predictable, and entirely self contained.
If an external system is required (parser, solver), the system should be mocked
and the test should focus on testing the piece of code that interacts with
that system.

It is understood that some functionalities are extremely difficult to unit
test properly. Thus it is perfectly ok to leave some complex task to be tested
by integration tests. A typical example would be ```codegen``` which basically
relies on the JVM.

New library functions or important changes to library functions warrant unit
tests.

### Integration Tests

Integration tests rely on one or more components of Leon. For instance, a test might rely on extraction to build a complex ```Program```, which is then used to test DefOps operations. Even though these tests are not self-contained, their dependencies can be assumed correct. This allows us to test parts/features that cannot easily be isolated: functions on large programs, solvers, code-gen evaluators.

### Regression Tests

Regression tests are meant to ensure that Leon behaves consistently as a whole on a large set of source files. Entire features of leon are tested by typically running a full pipeline on several file inputs. These tests are slow and are used by travis-ci to validate builds.

**Important:** If/When an regression test fails, the code fix must be accompanied with unit or integration tests that would have caught the issue. This is a on-demand path to transition from essentially only regression tests to smaller, focused tests.
