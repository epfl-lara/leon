#!/bin/bash

runner="./scalac-funcheck"
newargs=""

for arg in $@
do
    if [ -e ${arg} ]
    then
        newargs="${newargs} ${arg}"
    else
        newargs="${newargs} -P:funcheck:${arg}"
    fi
done

if [ -e ${runner} ]
then
    ${runner} -P:funcheck:CAV ${newargs} -P:funcheck:CAV
    exit 0
else
    echo "${runner} not found. Have you run 'sbt all' ?"
    exit 1
fi

