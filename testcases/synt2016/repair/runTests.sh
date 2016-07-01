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

function run {
  cmd="./leon --debug=report --timeout=60 --repair --introreccalls=off --solvers=fairz3,enum --functions=$1 $2"
  echo "Running " $cmd
  echo "------------------------------------------------------------------------------------------------------------------"
  $cmd | tee -a $fullLog
}

echo "=====================================================================" >> repair-report.txt

run desugar  testcases/synt2016/repair/Compiler/Compiler1.scala   
run desugar  testcases/synt2016/repair/Compiler/Compiler2.scala   
run desugar  testcases/synt2016/repair/Compiler/Compiler3.scala   
run desugar  testcases/synt2016/repair/Compiler/Compiler4.scala   
run desugar  testcases/synt2016/repair/Compiler/Compiler5.scala   
run simplify testcases/synt2016/repair/Compiler/Compiler6.scala   

run merge    testcases/synt2016/repair/Heap/Heap3.scala           
run merge    testcases/synt2016/repair/Heap/Heap4.scala           
run merge    testcases/synt2016/repair/Heap/Heap5.scala           
run merge    testcases/synt2016/repair/Heap/Heap6.scala           
run merge    testcases/synt2016/repair/Heap/Heap7.scala           
run merge    testcases/synt2016/repair/Heap/Heap10.scala          
run insert   testcases/synt2016/repair/Heap/Heap8.scala           
run makeN    testcases/synt2016/repair/Heap/Heap9.scala           

run pad      testcases/synt2016/repair/List/List1.scala           
run ++       testcases/synt2016/repair/List/List2.scala           
run :+       testcases/synt2016/repair/List/List3.scala           
run replace  testcases/synt2016/repair/List/List5.scala           
run count    testcases/synt2016/repair/List/List6.scala           
run find     testcases/synt2016/repair/List/List7.scala           
run find     testcases/synt2016/repair/List/List8.scala           
run find     testcases/synt2016/repair/List/List9.scala           
run size     testcases/synt2016/repair/List/List10.scala          
run sum      testcases/synt2016/repair/List/List11.scala          
run -        testcases/synt2016/repair/List/List12.scala          
run drop     testcases/synt2016/repair/List/List4.scala           
run drop     testcases/synt2016/repair/List/List13.scala          

run power    testcases/synt2016/repair/Numerical/Numerical1.scala 
run moddiv   testcases/synt2016/repair/Numerical/Numerical3.scala 

run split    testcases/synt2016/repair/MergeSort/MergeSort1.scala 
run merge    testcases/synt2016/repair/MergeSort/MergeSort2.scala 
run merge    testcases/synt2016/repair/MergeSort/MergeSort3.scala 
run merge    testcases/synt2016/repair/MergeSort/MergeSort4.scala 
run merge    testcases/synt2016/repair/MergeSort/MergeSort5.scala 

# Average results
#cat $log >> $summaryLog
#awk '{ total1 += $7; total2 += $8; total3 += $9; count++ } END { printf "#%74s Avg: %5d, %5d, %5d\n\n", "", total1/count, total2/count, total3/count }' $log >> $summaryLog

