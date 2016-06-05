set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for rotateDroptime vs orb inferred, n vs rotateDroptime"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/rotateDroptimeVsOrb.jpg"
plot \
"<(sed -n '1,1627p' results/orbrotateDroptime.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,1627p' results/opsrotateDroptime.data)" using 1:2 t'oper' with linespoints, 
