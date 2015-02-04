#!/bin/bash
log=repairs.last
fullLog=repairs.log

echo -n "" > $log;


echo "################################" >> $fullLog
echo "#" `hostname` >> $fullLog
echo "#" `date +"%d.%m.%Y %T"` >> $fullLog
echo "#" `git log -1 --pretty=format:"%h - %cd"` >> $fullLog
echo "################################" >> $fullLog
echo "#           Category,                 File,             function, p.S, fuS, foS,   Tms,   Fms,   Rms, verif?" >> $fullLog

#All benchmarks:
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar1.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar2.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar3.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar4.scala

./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort3.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort4.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort5.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort6.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort7.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=insert   testcases/repair/HeapSort/HeapSort8.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=makeN    testcases/repair/HeapSort/HeapSort9.scala

./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic1.scala 
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic2.scala 
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic3.scala 
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic4.scala 
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic5.scala 

./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_pad     testcases/repair/List/List1.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_ap      testcases/repair/List/List3.scala
./leon --repair --timeout=30                       --functions=_drop    testcases/repair/List/List4.scala
./leon --repair --timeout=30                       --functions=_replace testcases/repair/List/List5.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_count   testcases/repair/List/List6.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_find    testcases/repair/List/List7.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_find    testcases/repair/List/List8.scala
./leon --repair --timeout=30                       --functions=_find    testcases/repair/List/List9.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_size    testcases/repair/List/List10.scala
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=sum      testcases/repair/List/List11.scala

# Average results
cat $log >> $fullLog
awk '{ total1 += $7; total2 += $8; total3 += $9; count++ } END { printf "#%74s Avg: %5d, %5d, %5d\n\n", "", total1/count, total2/count, total3/count }' $log >> $fullLog

