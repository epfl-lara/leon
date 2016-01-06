#!/bin/bash

function run {
    cmd="./leon --debug=report --timeout=30 --synthesis $1"
    echo "Running " $cmd
    echo "------------------------------------------------------------------------------------------------------------------"
    $cmd;
}

echo "==================================================================================================================" >> synthesis-report.txt
# These are all the benchmarks included in my thesis
# List
run testcases/synthesis/etienne-thesis/List/Insert.scala
run testcases/synthesis/etienne-thesis/List/Delete.scala
run testcases/synthesis/etienne-thesis/List/Union.scala
run testcases/synthesis/etienne-thesis/List/Diff.scala
run testcases/synthesis/etienne-thesis/List/Split.scala

# SortedList
run testcases/synthesis/etienne-thesis/SortedList/Insert.scala
run testcases/synthesis/etienne-thesis/SortedList/InsertAlways.scala
run testcases/synthesis/etienne-thesis/SortedList/Delete.scala
run testcases/synthesis/etienne-thesis/SortedList/Union.scala
run testcases/synthesis/etienne-thesis/SortedList/Diff.scala
run testcases/synthesis/etienne-thesis/SortedList/InsertionSort.scala

# StrictSortedList
run testcases/synthesis/etienne-thesis/StrictSortedList/Insert.scala
run testcases/synthesis/etienne-thesis/StrictSortedList/Delete.scala
run testcases/synthesis/etienne-thesis/StrictSortedList/Union.scala

# UnaryNumerals
run testcases/synthesis/etienne-thesis/UnaryNumerals/Add.scala
run testcases/synthesis/etienne-thesis/UnaryNumerals/Distinct.scala
run testcases/synthesis/etienne-thesis/UnaryNumerals/Mult.scala

# BatchedQueue
#run testcases/synthesis/etienne-thesis/BatchedQueue/Enqueue.scala
run testcases/synthesis/etienne-thesis/BatchedQueue/Dequeue.scala

# AddressBook
#run testcases/synthesis/etienne-thesis/AddressBook/Make.scala
run testcases/synthesis/etienne-thesis/AddressBook/Merge.scala
