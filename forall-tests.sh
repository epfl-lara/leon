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


alias scalac=".././scalac-funcheck -cp ../bin:../lib/ScalaCheck-1.5.jar  -d ../bin/tests"

cd tests

scalac plugin/BST.scala
scalac plugin/LeftistHeap.scala

cd ..

# Scala compiler with the Funcheck plugin integrated
#alias scalac="./scalac-funcheck"

# compile examples using the compiler with the Funcheck plugin
#ant compile-funcheck-tests


echo
echo "********************************************************************************"
echo "Running tests with forAll properties."
echo "********************************************************************************"
echo

alias scala="scala -cp bin/:${SCALACHECK_JAR}:bin/tests/"

# examples
export BST="plugin.BST"
export LeftistHeap="plugin.LeftistHeap"

echo " - Testing ${BST}"
scala ${BST}

echo " - Testing ${LeftistHeap}"
scala ${LeftistHeap}

