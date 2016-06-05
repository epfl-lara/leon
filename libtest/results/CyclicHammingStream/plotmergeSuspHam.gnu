set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size mergeSuspHam"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualmergeSuspHam10.jpg"
plot \
"<(sed -n '1,20p' results/orbmergeSuspHam.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opsmergeSuspHam.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualmergeSuspHam100.jpg"
plot \
"<(sed -n '20,40p' results/orbmergeSuspHam.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opsmergeSuspHam.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualmergeSuspHam1000.jpg"
plot \
"<(sed -n '40,50p' results/orbmergeSuspHam.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opsmergeSuspHam.data)" using 1:2 t'oper' with linespoints, 
