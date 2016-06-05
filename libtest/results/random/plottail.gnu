set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size tail"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualtail10.jpg"
plot \
"<(sed -n '1,20p' results/orbtail.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opstail.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualtail100.jpg"
plot \
"<(sed -n '20,40p' results/orbtail.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opstail.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualtail1000.jpg"
plot \
"<(sed -n '40,50p' results/orbtail.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opstail.data)" using 1:2 t'oper' with linespoints, 
