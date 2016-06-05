set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for rotateRev vs orb inferred, n vs rotateRev"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/rotateRevVsOrb.jpg"
plot \
"<(sed -n '1,1560p' results/orbrotateRev.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,1560p' results/opsrotateRev.data)" using 1:2 t'oper' with linespoints, 
