#!/bin/bash

function run {
    cmd="./leon --debug=report --timeout=60 --synthesis --partial=off --solvers=smt-z3 $1"
    echo "Running " $cmd
    echo "------------------------------------------------------------------------------------------------------------------"
    $cmd;
}

echo "==================================================================================================================" >> synthesis-report.txt
# These are all the benchmarks included in my thesis
# List
run testcases/synthesis/current/List/Insert.scala
run testcases/synthesis/current/List/Delete.scala
run testcases/synthesis/current/List/Union.scala
run testcases/synthesis/current/List/Diff.scala
run testcases/synthesis/current/List/Split.scala
run testcases/synthesis/current/List/ListOfSize.scala

# SortedList
run testcases/synthesis/current/SortedList/Insert.scala
run testcases/synthesis/current/SortedList/InsertAlways.scala
run testcases/synthesis/current/SortedList/Delete.scala
run testcases/synthesis/current/SortedList/Union.scala
run testcases/synthesis/current/SortedList/Diff.scala
run testcases/synthesis/current/SortedList/InsertionSort.scala

# StrictSortedList
run testcases/synthesis/current/StrictSortedList/Insert.scala
run testcases/synthesis/current/StrictSortedList/Delete.scala
run testcases/synthesis/current/StrictSortedList/Union.scala

# UnaryNumerals
run testcases/synthesis/current/UnaryNumerals/Add.scala
run testcases/synthesis/current/UnaryNumerals/Distinct.scala
run testcases/synthesis/current/UnaryNumerals/Mult.scala

# BatchedQueue
run testcases/synthesis/current/BatchedQueue/Enqueue.scala
run testcases/synthesis/current/BatchedQueue/Dequeue.scala

# AddressBook
run testcases/synthesis/current/AddressBook/Make.scala
run testcases/synthesis/current/AddressBook/Merge.scala

# RunLength
run testcases/synthesis/current/RunLength/RunLength.scala

# Diffs
run testcases/synthesis/current/Diffs/Diffs.scala

