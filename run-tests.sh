#!/bin/sh

nbtests=$(ls -l testcases/regression/*valid/*.scala | wc -l)
nbsuccess=0
failedtests=""

for f in testcases/regression/valid/*.scala; do
  echo -n "Running $f, expecting VALID, got: "
  res=`./leon --timeout=5 --oneline "$f"`
  echo $res | tr [a-z] [A-Z]
  if [ $res = valid ]; then
    nbsuccess=$((nbsuccess + 1))
  else
    failedtests="$failedtests $f"
  fi
done

for f in testcases/regression/invalid/*.scala; do
  echo -n "Running $f, expecting INVALID, got: "
  res=`./leon --timeout=5 --oneline "$f"`
  echo $res | tr [a-z] [A-Z]
  if [ $res = invalid ]; then
    nbsuccess=$((nbsuccess + 1))
  else
    failedtests="$failedtests $f"
  fi
done

echo "$nbsuccess out of $nbtests tests were successful"
if [ $nbtests -eq $nbsuccess ]; then
  echo "PASSED"
else
  echo "ERROR. The following test did not run as expected:"
  for f in $failedtests; do echo $f; done
fi
