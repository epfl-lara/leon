#!/bin/bash

echo 
echo "********************************************************************************" 
echo "**                        COMPILE AND RUN EXAMPLES                            **"
echo "********************************************************************************"
echo

echo
echo "********************************************************************************"
echo "Compile and Build the distribution using ANT"
echo "********************************************************************************"
echo 

# first clean
#ant clean
# and build the distribution
ant dist

# Note:
# When the distribution is builded the script scalac-funcheck should be created.
# This will be used to compile the examples since the Funcheck compiler plugin
# will take care of transforming the Specs.forAll calls into ScalaCheck forAll
# ones.

echo
echo "********************************************************************************"
echo "Check that needed scripts and libraries are available."
echo "********************************************************************************"
echo

export SCALAC_SCRIPT="scalac-funcheck"
export SCALACHECK_JAR="lib/ScalaCheck-1.5.jar"

if [ -e "$SCALAC_SCRIPT" ]
then
    echo "[OK] ${SCALAC_SCRIPT} script found."
    if [ -e "${SCALACHECK_JAR}" ]
	then
		echo "[OK] ${SCALACHECK_JAR} found."
	else
	    echo "[ERROR] ${SCALACHECK_JAR} NOT found."
		echo "Please correct this and try again."
		return -1
	fi
else
	echo "[ERROR] ${SCALAC_SCRIPT} script NOT found."
	echo "Please correct this and try again."
	return -1
fi


echo
echo "********************************************************************************"
echo "Compile tests that have declared forAll properties."
echo "********************************************************************************"
echo


#This is needed for aliases to work correctly
shopt -s expand_aliases;


alias scalac="./scalac-funcheck -cp lib/ScalaCheck-1.5.jar:bin/lib/:bin/scala  -d bin/examples"

scalac examples/plugin/BST.scala
scalac examples/plugin/LeftistHeap.scala
scalac examples/plugin/ListSet.scala
scalac examples/plugin/LambdaEvaluator.scala
scalac examples/plugin/PropositionalLogic.scala
scalac examples/plugin/SetRedBlackTree.scala
scalac examples/plugin/ConsSnoc.scala

scalac examples/plugin/kawaguchi_pldi2010/InsertSort.scala
scalac examples/plugin/kawaguchi_pldi2010/MergeSort.scala
scalac examples/plugin/kawaguchi_pldi2010/MergeSortBug.scala
scalac examples/plugin/kawaguchi_pldi2010/QuickSort.scala
scalac examples/plugin/kawaguchi_pldi2010/MapReduce.scala
scalac examples/plugin/kawaguchi_pldi2010/SplayHeap.scala


# Scala compiler with the Funcheck plugin integrated
#alias scalac="./scalac-funcheck"

# compile examples using the compiler with the Funcheck plugin
#ant compile-funcheck-tests


echo
echo "********************************************************************************"
echo "Running tests with forAll properties."
echo "********************************************************************************"
echo

export CP="bin/:${SCALACHECK_JAR}:bin/scala:bin/examples/:bin/lib"
alias scala="scala -cp ${CP}"


# examples
export BST="plugin.BST"
export LeftistHeap="plugin.LeftistHeap"
export ListSet="plugin.ListSet"
export LambdaEvaluator="plugin.LambdaEvaluator"
export PropositionalLogic="plugin.PropositionalLogic"
export SetRedBlackTree="plugin.SetRedBlackTree"
export ConsSnoc="plugin.ConsSnoc"

export InsertSort="plugin.kawaguchi_pldi2010.InsertSort"
export MergeSort="plugin.kawaguchi_pldi2010.MergeSort"
export MergeSortBug="plugin.kawaguchi_pldi2010.MergeSortBug"
export QuickSort="plugin.kawaguchi_pldi2010.QuickSort"
export MapReduce="plugin.kawaguchi_pldi2010.MapReduce"
export SplayHeap="plugin.kawaguchi_pldi2010.SplayHeap"

echo " - Testing ${BST}"
scala ${BST}

echo " - Testing ${LeftistHeap}"
scala ${LeftistHeap}

echo " - Testing ${ListSet}"
scala ${ListSet}

echo " - Testing ${SetRedBlackTree}"
scala ${SetRedBlackTree}

echo " - Testing ${LambdaEvaluator}"
scala ${LambdaEvaluator}

echo " - Testing ${PropositionalLogic}"
scala ${PropositionalLogic}

echo " - Testing ${ConsSnoc}"
scala ${ConsSnoc}

echo " - Testing ${InsertSort}"
scala ${InsertSort}

echo " - Testing ${MergeSort}"
scala ${MergeSort}

echo " - Testing ${MergeSortBug}. !!! EXPECTED TO CRASH !!!!"
scala ${MergeSortBug} 2> /dev/null | head -n 4

echo " - Testing ${QuickSort}"
scala ${QuickSort}

echo " - Testing ${MapReduce}"
scala ${MapReduce}

echo " - Testing ${SplayHeap}"
scala ${SplayHeap}
