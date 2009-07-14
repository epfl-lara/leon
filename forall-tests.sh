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


alias scalac="./scalac-funcheck"

ant compile-examples

# Scala compiler with the Funcheck plugin integrated
#alias scalac="./scalac-funcheck"

# compile examples using the compiler with the Funcheck plugin
#ant compile-funcheck-tests


echo
echo "********************************************************************************"
echo "Running tests with forAll properties."
echo "********************************************************************************"
echo

export CP="bin/:${SCALACHECK_JAR}:dist/funcheck-plugin.jar:bin/scala:bin/examples/:bin/lib"
alias scala="scala -cp ${CP}"


# examples
export BST="funcheck.BST"
export LeftistHeap="funcheck.LeftistHeap"
export ListSet="funcheck.ListSet"
export LambdaEvaluator="funcheck.LambdaEvaluator"
export PropositionalLogic="funcheck.PropositionalLogic"
export SetRedBlackTree="funcheck.SetRedBlackTree"
export ConsSnoc="funcheck.ConsSnoc"

export InsertSort="funcheck.kawaguchi_pldi2010.InsertSort"
export MergeSort="funcheck.kawaguchi_pldi2010.MergeSort"
export MergeSortBug="funcheck.kawaguchi_pldi2010.MergeSortBug"
export QuickSort="funcheck.kawaguchi_pldi2010.QuickSort"
export MapReduce="funcheck.kawaguchi_pldi2010.MapReduce"
export SplayHeap="funcheck.kawaguchi_pldi2010.SplayHeap"

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
