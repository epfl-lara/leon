set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size reverse"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualreverse10.jpg"
plot \
"<(sed -n '1,20p' results/orbreverse.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opsreverse.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualreverse100.jpg"
plot \
"<(sed -n '20,40p' results/orbreverse.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opsreverse.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualreverse1000.jpg"
plot \
"<(sed -n '40,50p' results/orbreverse.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opsreverse.data)" using 1:2 t'oper' with linespoints, 
