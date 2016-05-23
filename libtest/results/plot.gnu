set terminal jpeg

set key left top

set xlabel "n"
set ylabel "alloc"
set title "Plot for Orb vs Runnable code"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActual10.jpg"
plot \
"<(sed -n '1,20p' results/orb.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/ops.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActual100.jpg"
plot \
"<(sed -n '20,40p' results/orb.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/ops.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActual1000.jpg"
plot \
"<(sed -n '40,50p' results/orb.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/ops.data)" using 1:2 t'oper' with linespoints, 



