set datafile separator ","
set ylabel "Time (s)"
set xlabel "Number of lines generated"
set logscale y
set terminal pngcairo
set output "timings.png"
plot "timings" using 1:2 title "OCaml" with linespoints, \
     "timings" using 1:3 title "ChaML" with linespoints, \
     "timings" using 1:4 title "ATTAPL" with linespoints,\
     "timings" using 1:5 title "MLF" with linespoints
