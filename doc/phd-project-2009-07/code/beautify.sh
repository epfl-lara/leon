#!/bin/sh

rm -f *.cute

for src in *.scala ; do
    cat ${src} | \
    sed -e "s/==>/$\\\\rightarrow$/g" | \
    sed -e "s/=>/$\\\\Rightarrow$/g" | \
    sed -e "s/!=/$\\\\neq$/g" |
    sed -e "s/==/=/g" |
    cat > ${src}.cute
done
