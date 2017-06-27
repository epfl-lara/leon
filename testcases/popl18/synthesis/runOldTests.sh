#!/bin/bash

function run {
    cmd="./leon --debug=report --timeout=60 --synthesis --partial=off \
         --mode=manual --manual:script=$1 $2"
    echo "Running " $cmd
    echo "------------------------------------------------------------------------------------------------------------------"
    $cmd;
}

echo "==================================================================================================================" >> synthesis-report.txt
# List
: '
run 1 testcases/synt2016/synthesis/List/Insert.scala
run 4,0,1,1,0,0,3,0,1,1,1,2,1 testcases/synt2016/synthesis/List/Delete.scala
              # 2 
run 3,0,1,1,0,0,1 testcases/synt2016/synthesis/List/Union.scala
run 4,0,1,1,0,0,1 testcases/synt2016/synthesis/List/Diff.scala
run 3,0,0,1,0,0,0,0,1 testcases/synt2016/synthesis/List/Split.scala
run 3,0,0,1,0,0,1 testcases/synt2016/synthesis/List/ListOfSize.scala

# SortedList
run 4,0,1,1,0,0,3,0,1,1,1,2,1 testcases/synt2016/synthesis/SortedList/Insert.scala
run 4,0,1,1,0,0,3,0,1,1,1,2,1 testcases/synt2016/synthesis/SortedList/InsertAlways.scala
run 4,0,1,1,0,0,3,0,1,1,1,2,1 testcases/synt2016/synthesis/SortedList/Delete.scala
              # 2
run 3,0,1,1,0,0,1 testcases/synt2016/synthesis/SortedList/Union.scala
run 4,0,1,1,0,0,1 testcases/synt2016/synthesis/SortedList/Diff.scala
run 3,0,0,1,0,0,1 testcases/synt2016/synthesis/SortedList/InsertionSort.scala

# StrictSortedList
run 4,0,1,1,0,0,3,0,1,1,1,2,1 testcases/synt2016/synthesis/StrictSortedList/Insert.scala
run 4,0,1,1,0,0,3,0,1,1,1,2,1 testcases/synt2016/synthesis/StrictSortedList/Delete.scala
              # 2
run 3,0,1,1,0,0,1 testcases/synt2016/synthesis/StrictSortedList/Union.scala

# UnaryNumerals
run 3,0,1,1,0,0,1 testcases/synt2016/synthesis/UnaryNumerals/Add.scala
run 1             testcases/synt2016/synthesis/UnaryNumerals/Distinct.scala
run 3,0,1,1,0,0,1 testcases/synt2016/synthesis/UnaryNumerals/Mult.scala

# BatchedQueue
run 0,0,3,0,1,1,1 testcases/synt2016/synthesis/BatchedQueue/Enqueue.scala
run 0,0,3,0,1,1,3,0,1,1,1 testcases/synt2016/synthesis/BatchedQueue/Dequeue.scala

# AddressBook
run 3,0,0,1,0,0,0,0,0,0,3,0,1,1,1 testcases/synt2016/synthesis/AddressBook/Make.scala '
run 0,0,1 testcases/synt2016/synthesis/AddressBook/Merge.scala

# RunLength
run 3,0,0,1,0,0,4,0,1,1,0,0,3,0,1,1,1 testcases/synt2016/synthesis/RunLength/RunLength.scala

# Diffs
run 3,0,0,1,0,0,5,0,1,1,1 testcases/synt2016/synthesis/Diffs/Diffs.scala

