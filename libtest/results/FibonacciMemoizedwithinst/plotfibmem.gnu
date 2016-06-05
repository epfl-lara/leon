set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for inst vs Runnable code, size fibmem"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/instVsActualfibmem10.jpg"
plot \
"<(sed -n '1,20p' results/instfibmem.data)" using 1:2 t'inst' with linespoints, \
"<(sed -n '1,20p' results/opsfibmem.data)" using 1:2 t'oper' with linespoints, 

set output "results/instVsActualfibmem100.jpg"
plot \
"<(sed -n '20,40p' results/instfibmem.data)" using 1:2 t'inst' with linespoints, \
"<(sed -n '20,40p' results/opsfibmem.data)" using 1:2 t'oper' with linespoints,

set output "results/instVsActualfibmem1000.jpg"
plot \
"<(sed -n '40,50p' results/instfibmem.data)" using 1:2 t'inst' with linespoints, \
"<(sed -n '40,50p' results/opsfibmem.data)" using 1:2 t'oper' with linespoints, 
