set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for takelazycount vs orb inferred, n vs takelazycount"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/takelazycountVsOrb.jpg"
plot \
"<(sed -n '1,1627p' results/orbtakelazycount.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,1627p' results/opstakelazycount.data)" using 1:2 t'oper' with linespoints, 
