## How to benchmark Orb's count with actual operation count

Whenever a code gets instrumented, the `RunnableCodePhase` ensures that a runnable code is put into
`leon.out`. However, the code might not directly compile as it will depend on the library. Hence,
copy it into the `src/` directory of the current test project.

Example: <br/>
From the root directory, do
```
./leon --instrument ./testcases/orb-testcases/timing/InsertionSort.scala <br/>
cp ./leon.out/InsertionSort.scala ./testcases/runnablecode/src/
```

This shall now compile. <br/>
Use the `main` template as defined in `template/template.scala` to do the necessary benchmarks
