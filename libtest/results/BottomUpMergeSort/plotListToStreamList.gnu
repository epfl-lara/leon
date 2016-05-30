set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for Orb vs Runnable code, ListToStreamList"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualListToStreamList10.jpg"
plot \
"<(sed -n '1,20p' results/orbListToStreamList.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opsListToStreamList.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualListToStreamList100.jpg"
plot \
"<(sed -n '20,40p' results/orbListToStreamList.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opsListToStreamList.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualListToStreamList1000.jpg"
plot \
"<(sed -n '40,50p' results/orbListToStreamList.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opsListToStreamList.data)" using 1:2 t'oper' with linespoints, 
