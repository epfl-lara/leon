# Leon Coding Guidelines


Here are a few coding guidelines that should be followed when introducing new
code into Leon. Existing code that do not meet these guidelines should eventually
be fixed.

## Development

#### Global state must be concurrent-friendly

Leon relies on global state at several places, it should be assumed that this global state can be accessed concurrently, it is thus necessary to ensure that it will behave consistently. Global state should be ```private[this]``` and accessor functions **synchronized**. Another possibility for things like counters is to rely on Java classes such as ```AtomicInteger```.

Even though most of Leon is sequential, parts of it is concurrent (Portfolio Solvers, Web interface, Interrupt threads, ...). It is likely to become more concurrent in the future.

#### Code should be predictable

Leon's execution should be predictable and reproducible. Due to the complex nature of its inner-working, it is crucial that problematic executions and bug reports are consistently reproducible.

One of the main reason behind this unpredictability is the traversal of structures that are not explicitly ordered(e.g. ``Set``, ``Map``, ..). Please avoid that by either explicitly ordering after ``.toSeq``, or by using different datastructures.


## Testing

Leon tests are separated in unit-tests and integration tests. ```sbt test``` should run unit-tests only, integration tests are no longer expected to be routinely tested by developers when pushing new code (see below).


### Unit Tests

Leon should have unit-tests for commonly used functions, since most of these functions rely on a program, it is generally ok to obtain such program by extracting one from a .scala source file. It would be best if a somewhat generic but complete program could be re-used by many unit-tests.

New library functions or important changes to library functions warrant unit tests.

### Integration Tests

Integration tests check that Leon works as expected as a whole, by running it on an entire file and checking its results. These tests are slow and should only be used by travis-ci to validate builds.

**Important:** If/When an integration test fails, the code fix must be accompanied with unit-tests that would have caught the bug. This is a on-demand path to transition from integration tests to unit-tests.

