d=`date +%Y-%m-%d --date="2 days ago"`
dir=$(cd -P -- "$(dirname -- "$0")" && pwd -P)
mkdir -p $dir/builds
curl http://cvc4.cs.nyu.edu/builds/x86_64-linux-opt/unstable/cvc4-$d-x86_64-linux-opt -o $dir/builds/cvc4

chmod u+x $dir/builds/cvc4

export PATH=$dir/builds/:$PATH
