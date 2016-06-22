#!/bin/bash
log=repairs.last
summaryLog=repairs.log
fullLog=fullLog.log

echo -n "" > $log;
echo -n "" > "repairs.table";


echo "################################" >> $summaryLog
echo "#" `hostname` >> $summaryLog
echo "#" `date +"%d.%m.%Y %T"` >> $summaryLog
echo "#" `git log -1 --pretty=format:"%h - %cd"` >> $summaryLog
echo "################################" >> $summaryLog
echo "#           Category,                 File,             function, p.S, fuS, foS,   Tms,   Fms,   Rms, verif?" >> $summaryLog

#All benchmarks:

echo "=====================================================================" >> repair-report.txt

./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=desugar  testcases/synt2016/repair/Compiler/Compiler1.scala   | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=desugar  testcases/synt2016/repair/Compiler/Compiler2.scala   | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=desugar  testcases/synt2016/repair/Compiler/Compiler3.scala   | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=desugar  testcases/synt2016/repair/Compiler/Compiler4.scala   | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=desugar  testcases/synt2016/repair/Compiler/Compiler5.scala   | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=simplify testcases/synt2016/repair/Compiler/Compiler6.scala   | tee -a $fullLog

./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/Heap/Heap3.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/Heap/Heap4.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/Heap/Heap5.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/Heap/Heap6.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/Heap/Heap7.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/Heap/Heap10.scala          | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=insert   testcases/synt2016/repair/Heap/Heap8.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=makeN    testcases/synt2016/repair/Heap/Heap9.scala           | tee -a $fullLog

./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=pad      testcases/synt2016/repair/List/List1.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=++       testcases/synt2016/repair/List/List2.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=:+       testcases/synt2016/repair/List/List3.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60                       --functions=replace  testcases/synt2016/repair/List/List5.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=count    testcases/synt2016/repair/List/List6.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=find     testcases/synt2016/repair/List/List7.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=find     testcases/synt2016/repair/List/List8.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60                       --functions=find     testcases/synt2016/repair/List/List9.scala           | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=size     testcases/synt2016/repair/List/List10.scala          | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=sum      testcases/synt2016/repair/List/List11.scala          | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=-        testcases/synt2016/repair/List/List12.scala          | tee -a $fullLog
./leon --debug=report --repair --timeout=60                       --functions=drop     testcases/synt2016/repair/List/List4.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=drop     testcases/synt2016/repair/List/List13.scala          | tee -a $fullLog

./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=power    testcases/synt2016/repair/Numerical/Numerical1.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=moddiv   testcases/synt2016/repair/Numerical/Numerical3.scala | tee -a $fullLog

./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=split    testcases/synt2016/repair/MergeSort/MergeSort1.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/MergeSort/MergeSort2.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/MergeSort/MergeSort3.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/MergeSort/MergeSort4.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=60 --solvers=fairz3,enum --functions=merge    testcases/synt2016/repair/MergeSort/MergeSort5.scala | tee -a $fullLog

# Average results
#cat $log >> $summaryLog
#awk '{ total1 += $7; total2 += $8; total3 += $9; count++ } END { printf "#%74s Avg: %5d, %5d, %5d\n\n", "", total1/count, total2/count, total3/count }' $log >> $summaryLog

