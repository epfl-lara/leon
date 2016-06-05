set terminal jpeg

set key left top

set xlabel "log(n)"
set ylabel "time"
set title "Plot for orb vs Runnable code, log size vs incAndPay"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualincAndPay.jpg"
plot \
"<(sed -n '1,18p' results/orbincAndPay.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,18p' results/opsincAndPay.data)" using 1:2 t'oper' with linespoints, 
