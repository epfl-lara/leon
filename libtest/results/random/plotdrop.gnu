set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for drop vs orb inferred, n vs drop"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/dropVsOrb.jpg"
plot \
"<(sed -n '1,42450p' results/orbdrop.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,42450p' results/opsdrop.data)" using 1:2 t'oper' with linespoints, 
