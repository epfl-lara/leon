set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for Orb vs Runnable code, kthMin"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualkthMin10.jpg"
plot \
"<(sed -n '1,20p' results/orbkthMin.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opskthMin.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualkthMin100.jpg"
plot \
"<(sed -n '20,40p' results/orbkthMin.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opskthMin.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualkthMin1000.jpg"
plot \
"<(sed -n '40,50p' results/orbkthMin.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opskthMin.data)" using 1:2 t'oper' with linespoints, 
