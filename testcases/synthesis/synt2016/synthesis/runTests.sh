#!/bin/bash

function run {
    cmd="./leon --debug=report --timeout=60 --synthesis --partial=off $1"
    echo "Running " $cmd
    echo "------------------------------------------------------------------------------------------------------------------"
    $cmd;
}

echo "==================================================================================================================" >> synthesis-report.txt
# List
run testcases/synthesis/synt2016/synthesis/List/Insert.scala
run testcases/synthesis/synt2016/synthesis/List/Delete.scala
run testcases/synthesis/synt2016/synthesis/List/Union.scala
run testcases/synthesis/synt2016/synthesis/List/Diff.scala
run testcases/synthesis/synt2016/synthesis/List/Split.scala
run testcases/synthesis/synt2016/synthesis/List/ListOfSize.scala

# SortedList
run testcases/synthesis/synt2016/synthesis/SortedList/Insert.scala
run testcases/synthesis/synt2016/synthesis/SortedList/InsertAlways.scala
run testcases/synthesis/synt2016/synthesis/SortedList/Delete.scala
run testcases/synthesis/synt2016/synthesis/SortedList/Union.scala
run testcases/synthesis/synt2016/synthesis/SortedList/Diff.scala
run testcases/synthesis/synt2016/synthesis/SortedList/InsertionSort.scala

# StrictSortedList
run testcases/synthesis/synt2016/synthesis/StrictSortedList/Insert.scala
run testcases/synthesis/synt2016/synthesis/StrictSortedList/Delete.scala
run testcases/synthesis/synt2016/synthesis/StrictSortedList/Union.scala

# UnaryNumerals
run testcases/synthesis/synt2016/synthesis/UnaryNumerals/Add.scala
run testcases/synthesis/synt2016/synthesis/UnaryNumerals/Distinct.scala
run testcases/synthesis/synt2016/synthesis/UnaryNumerals/Mult.scala

# BatchedQueue
run testcases/synthesis/synt2016/synthesis/BatchedQueue/Enqueue.scala
run testcases/synthesis/synt2016/synthesis/BatchedQueue/Dequeue.scala

# AddressBook
run testcases/synthesis/synt2016/synthesis/AddressBook/Make.scala
run testcases/synthesis/synt2016/synthesis/AddressBook/Merge.scala

# RunLength
run testcases/synthesis/synt2016/synthesis/RunLength/RunLength.scala

# Diffs
run testcases/synthesis/synt2016/synthesis/Diffs/Diffs.scala

