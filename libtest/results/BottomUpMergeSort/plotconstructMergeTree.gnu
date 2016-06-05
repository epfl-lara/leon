set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for Orb vs Runnable code, constructMergeTree"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualconstructMergeTree10.jpg"
plot \
"<(sed -n '1,20p' results/orbconstructMergeTree.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opsconstructMergeTree.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualconstructMergeTree100.jpg"
plot \
"<(sed -n '20,40p' results/orbconstructMergeTree.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opsconstructMergeTree.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualconstructMergeTree1000.jpg"
plot \
"<(sed -n '40,50p' results/orbconstructMergeTree.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opsconstructMergeTree.data)" using 1:2 t'oper' with linespoints, 
