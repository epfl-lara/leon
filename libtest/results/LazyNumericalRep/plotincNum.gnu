set terminal jpeg

set key left top

set xlabel "log(n)"
set ylabel "time"
set title "Plot for orb vs Runnable code, log size vs incNum"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualincNum.jpg"
plot \
"<(sed -n '1,18p' results/orbincNum.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,18p' results/opsincNum.data)" using 1:2 t'oper' with linespoints, 
