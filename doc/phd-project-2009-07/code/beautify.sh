#!/bin/sh

rm -f *.cute

for src in *.scala ; do
    sed -e "s/=>/$\\\\Rightarrow$/g" ${src} | \
    sed -e "s/!=/$\\\\neq$/g" |
    sed -e "s/==/=/g" > ${src}.cute
done
