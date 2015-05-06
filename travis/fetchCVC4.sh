dir=$(cd -P -- "$(dirname -- "$0")" && pwd -P)
mkdir -p $dir/builds
curl http://lara.epfl.ch/~ekneuss/cvc4-builds/cvc4-2015-04-17-x86_64-linux-opt -o $dir/builds/cvc4

chmod u+x $dir/builds/cvc4

export PATH=$dir/builds/:$PATH
