set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size zipWithFunFib"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualzipWithFunFib10.jpg"
plot \
"<(sed -n '1,20p' results/orbzipWithFunFib.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opszipWithFunFib.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualzipWithFunFib100.jpg"
plot \
"<(sed -n '20,40p' results/orbzipWithFunFib.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opszipWithFunFib.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualzipWithFunFib1000.jpg"
plot \
"<(sed -n '40,50p' results/orbzipWithFunFib.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opszipWithFunFib.data)" using 1:2 t'oper' with linespoints, 
