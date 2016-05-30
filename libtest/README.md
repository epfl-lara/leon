This file resides in `./libtest` and provides instructions to benchmark lazy and mem functions.

Two ways of benchmarking possible:
1. Compare the number of operations(`runnable`) with Orb results.
2.  Compare `runnable` with `withinst` file to check model.

### 1. Benchmarking

The files are in `src/benchmark`. You may wish to do the follow:
* Use new Orb results: Just change the formula while constructing `orb`.
* Use newly obtained `runnable` code (*). Overwrite everything but retain the main.

(*) For this get the source from `leon.out` once you have executed with `--runnable` option. Then remove `****` before `lookup` and `update`
 and fix their names. Also remove unused data-structures, one thumb rule is for data-structures with same name retain the one with highest numerical
 suffix. You can use the script `runnable.py` which takes in the argument as the filename at your own risk. It automatically picks file from `leon.out`
 and dumps it into `src/main/scala/benchmark` directory.

### 2. Testing Model

The files are in `src/benchmark` suffix-ed `withinst`. You may wish to do the follow:
* Use new `runnable` code. Follow instructions(*) above.
* Use new `withinst` code. Run with `mem` option and use the `withrun` suffix-ed dump in `leon.out` (#)

(#)

README ends here.