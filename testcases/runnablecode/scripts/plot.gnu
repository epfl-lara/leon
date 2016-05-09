set terminal jpeg

set output "orbVsActual.jpg"

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for Orb vs Runnable code"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

plot \
'numbers-runnable.data' using 1:2 t'orb' with linespoints, \
'numbers-set-1.data' using 1:2 t'run1' with linespoints, \
'numbers-set-2.data' using 1:2 t'run2' with linespoints,
