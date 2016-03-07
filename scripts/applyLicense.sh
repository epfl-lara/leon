printf "/* Copyright 2009-2016 EPFL, Lausanne */\n\n" > /tmp/Leon-license

for f in $(find {src,library} -name "*.java" -o -name "*.scala") ;do
  if [ -f $f ]; then
      cat "/tmp/Leon-license" > /tmp/newfile
      if  grep -Fq "EPFL, Lausanne" "$f";
      then
          tail -n +3 $f >> /tmp/newfile
      else
          cat $f >> /tmp/newfile
      fi
      if ! cmp --silent /tmp/newfile "$f"; then
          echo $f
          mv /tmp/newfile "$f"
      fi
  fi
done
