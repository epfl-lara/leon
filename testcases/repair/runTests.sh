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

#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=desugar  testcases/repair/Compiler/Compiler1.scala   | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=desugar  testcases/repair/Compiler/Compiler2.scala   | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=desugar  testcases/repair/Compiler/Compiler3.scala   | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=desugar  testcases/repair/Compiler/Compiler4.scala   | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=desugar  testcases/repair/Compiler/Compiler5.scala   | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=simplify testcases/repair/Compiler/Compiler6.scala   | tee -a $fullLog


#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/Heap/Heap3.scala        | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/Heap/Heap4.scala        | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/Heap/Heap5.scala        | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/Heap/Heap6.scala        | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/Heap/Heap7.scala        | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/Heap/Heap10.scala       | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=insert   testcases/repair/Heap/Heap8.scala        | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=makeN    testcases/repair/Heap/Heap9.scala        | tee -a $fullLog

#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=nnf      testcases/repair/PropLogic/PropLogic1.scala | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=nnf      testcases/repair/PropLogic/PropLogic2.scala | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=nnf      testcases/repair/PropLogic/PropLogic3.scala | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=nnf      testcases/repair/PropLogic/PropLogic4.scala | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=nnf      testcases/repair/PropLogic/PropLogic5.scala | tee -a $fullLog

#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=pad     testcases/repair/List/List1.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=++      testcases/repair/List/List2.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=:+      testcases/repair/List/List3.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30                       --functions=replace testcases/repair/List/List5.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=count   testcases/repair/List/List6.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=find    testcases/repair/List/List7.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=find    testcases/repair/List/List8.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30                       --functions=find    testcases/repair/List/List9.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=size    testcases/repair/List/List10.scala          | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=sum     testcases/repair/List/List11.scala          | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=-       testcases/repair/List/List12.scala          | tee -a $fullLog
#./leon --debug=report --repair --timeout=30                       --functions=drop    testcases/repair/List/List4.scala           | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=drop    testcases/repair/List/List13.scala          | tee -a $fullLog

#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=power    testcases/repair/Numerical/Numerical1.scala | tee -a $fullLog
#./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=moddiv   testcases/repair/Numerical/Numerical3.scala | tee -a $fullLog

./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=split    testcases/repair/MergeSort/MergeSort1.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/MergeSort/MergeSort2.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/MergeSort/MergeSort3.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/MergeSort/MergeSort4.scala | tee -a $fullLog
./leon --debug=report --repair --timeout=30 --solvers=fairz3,enum --functions=merge    testcases/repair/MergeSort/MergeSort5.scala | tee -a $fullLog

# Average results
#cat $log >> $summaryLog
#awk '{ total1 += $7; total2 += $8; total3 += $9; count++ } END { printf "#%74s Avg: %5d, %5d, %5d\n\n", "", total1/count, total2/count, total3/count }' $log >> $summaryLog

