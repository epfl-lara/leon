#!/bin/bash
log=stringrender.last
summaryLog=stringrender.log
fullLog=fullLog.log

echo -n "" > $log;
echo -n "" > "stringrender.table";


echo "################################" >> $summaryLog
echo "#" `hostname` >> $summaryLog
echo "#" `date +"%d.%m.%Y %T"` >> $summaryLog
echo "#" `git log -1 --pretty=format:"%h - %cd"` >> $summaryLog
echo "################################" >> $summaryLog
echo "#           Category,                 File,             function, p.S, fuS, foS,   Tms,   Fms,   Rms, verif?" >> $summaryLog

#All benchmarks:
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairUnWrapped          testcases/stringrender/IntWrapperRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairNameChangedPrefix  testcases/stringrender/IntWrapperRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairNameChangedSuffix  testcases/stringrender/IntWrapperRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairDuplicate          testcases/stringrender/IntWrapperRender.scala     | tee -a $fullLog

./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairUnWrapped          testcases/stringrender/TupleWrapperRender.scala   | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairNameChangedPrefix  testcases/stringrender/TupleWrapperRender.scala   | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairNameChangedSuffix  testcases/stringrender/TupleWrapperRender.scala   | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=repairDuplicate          testcases/stringrender/TupleWrapperRender.scala   | tee -a $fullLog

./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render1RemoveCons        testcases/stringrender/ListRender.scala           | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render2RemoveNil         testcases/stringrender/ListRender.scala           | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render3RemoveLastComma   testcases/stringrender/ListRender.scala           | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render4RemoveParentheses testcases/stringrender/ListRender.scala           | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render5WrapParentheses   testcases/stringrender/ListRender.scala           | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render6List              testcases/stringrender/ListRender.scala           | tee -a $fullLog

./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render0RemoveBigInt      testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render1RemoveCons        testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render2RemoveNil         testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render3RemoveLastComma   testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render4RemoveParentheses testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render5WrapParentheses   testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render6List              testcases/stringrender/ListBigIntRender.scala     | tee -a $fullLog

./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render0RemoveNames       testcases/stringrender/GrammarRender.scala        | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render1ArrowRules        testcases/stringrender/GrammarRender.scala        | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render2ListRules         testcases/stringrender/GrammarRender.scala        | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render3SpaceRules        testcases/stringrender/GrammarRender.scala        | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render4HTMLRules         testcases/stringrender/GrammarRender.scala        | tee -a $fullLog
./leon --stringrender --timeout=30 --solvers=fairz3,enum --functions=render5PlainTextRules    testcases/stringrender/GrammarRender.scala        | tee -a $fullLog


# Average results
cat $log >> $summaryLog
awk '{ total1 += $7; total2 += $8; total3 += $9; count++ } END { printf "#%74s Avg: %5d, %5d, %5d\n\n", "", total1/count, total2/count, total3/count }' $log >> $summaryLog

