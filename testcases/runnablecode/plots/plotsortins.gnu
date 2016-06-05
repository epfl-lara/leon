set terminal jpeg

set output "sortinsorbVsActual.jpg"

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for sort ins,Orb vs Runnable code"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

plot \
'sortins-runnable.data' using 1:2 t'runtime' with linespoints, \
'sortins-orb1.data' using 1:2 t'orb1' with linespoints, \
'sortins-orb2.data' using 1:2 t'orb2' with linespoints,
