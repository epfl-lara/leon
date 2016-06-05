set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for revappend vs orb inferred, n vs revappend"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/revappendVsOrb.jpg"
plot \
"<(sed -n '1,24921p' results/orbrevappend.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,24921p' results/opsrevappend.data)" using 1:2 t'oper' with linespoints, 
