#!/bin/sh
(cd .. && make)
x=1;
rm -f timings
max=14
ulimit -s 1000000
echo -n "0/$max"
while [ $x -le $max ]; do
  echo -n "\r$x/$max";
  # Generate test file
  ocaml gen.ml $x ocaml > boris.ml
  ocaml gen.ml $x attapl > boris_attapl.ml
  ocaml gen.ml $x mlf > boris_mlf.ml
  # Timings
  t1=0
  #t1=$(/usr/bin/time --format "%U" ocamlc.opt boris.ml 2>&1 > /dev/null)
  t2=0
  t2=$(/usr/bin/time --format "%U" ../chaml.native --dont-print-types --im-feeling-lucky boris.ml 2>&1 > /dev/null)
  t3=0
  t3=$(/usr/bin/time --format "%U" mini --end solve-constraint boris_attapl.ml 2>&1 > /dev/null)
  t4=0
  t4=$(/usr/bin/time --format "%U" mlf < boris_mlf.ml 2>&1 > /dev/null)
  echo "$x,$t1,$t2,$t3,$t4" >> timings
  x=$(($x+1));
done;
echo " ...done"
gnuplot script.gnuplot
eog timings.png
cat timings
rm -f boris.cm* boris*.ml
rm -f timings.png timings
