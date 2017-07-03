#!/bin/bash

grammar1=testcases/popl18/Grammar1-tags.scala
grammar2=testcases/popl18/Grammar2.scala

axioms1=on
axioms2=off

function run {
    cmd="./leon --debug=report --timeout=60 --synthesis --userdefined --partial=off \
         --mode=manual --manual:script=$1 $grammar2 --probwise:axioms=$axioms2 $2"
    echo "Running " $cmd
    echo "------------------------------------------------------------------------------------------------------------------"
    $cmd;
}

echo "==================================================================================================================" >> synthesis-report.txt
# List
run 2 testcases/popl18/synthesis/List/Insert.scala
run 4,0,2,1,0,0,3,0,2,1,2,2,2 testcases/popl18/synthesis/List/Delete.scala
              # 2 
run 3,0,2,1,0,0,2 testcases/popl18/synthesis/List/Union.scala
run 4,0,2,1,0,0,2 testcases/popl18/synthesis/List/Diff.scala
run 3,0,0,1,0,0,0,0,2 testcases/popl18/synthesis/List/Split.scala
run 3,0,0,1,0,0,2 testcases/popl18/synthesis/List/ListOfSize.scala

# SortedList
run 4,0,2,1,0,0,3,0,2,1,2,2,2 testcases/popl18/synthesis/SortedList/Insert.scala
run 4,0,2,1,0,0,3,0,2,1,2,2,2 testcases/popl18/synthesis/SortedList/InsertAlways.scala
run 4,0,2,1,0,0,3,0,2,1,2,2,2 testcases/popl18/synthesis/SortedList/Delete.scala
              # 2
run 3,0,2,1,0,0,2 testcases/popl18/synthesis/SortedList/Union.scala
run 4,0,2,1,0,0,2 testcases/popl18/synthesis/SortedList/Diff.scala
run 3,0,0,1,0,0,2 testcases/popl18/synthesis/SortedList/InsertionSort.scala

# StrictSortedList
run 4,0,2,1,0,0,3,0,2,1,2,2,2 testcases/popl18/synthesis/StrictSortedList/Insert.scala
run 4,0,2,1,0,0,3,0,2,1,2,2,2 testcases/popl18/synthesis/StrictSortedList/Delete.scala
              # 2
run 3,0,2,1,0,0,2 testcases/popl18/synthesis/StrictSortedList/Union.scala

# UnaryNumerals
run 3,0,2,1,0,0,2 testcases/popl18/synthesis/UnaryNumerals/Add.scala
run 2             testcases/popl18/synthesis/UnaryNumerals/Distinct.scala
run 3,0,2,1,0,0,2 testcases/popl18/synthesis/UnaryNumerals/Mult.scala

# BatchedQueue
run 0,0,3,0,2,1,2 testcases/popl18/synthesis/BatchedQueue/Enqueue.scala
run 0,0,3,0,2,1,3,0,2,1,2 testcases/popl18/synthesis/BatchedQueue/Dequeue.scala

# AddressBook
run 3,0,0,1,0,0,0,0,0,0,3,0,2,1,2 testcases/popl18/synthesis/AddressBook/Make.scala
run 0,0,2 testcases/popl18/synthesis/AddressBook/Merge.scala

# RunLength
run 3,0,0,1,0,0,4,0,2,1,0,0,3,0,2,1,2 testcases/popl18/synthesis/RunLength/RunLength.scala

# Diffs
run 3,0,0,1,0,0,5,0,2,1,2 testcases/popl18/synthesis/Diffs/Diffs.scala

