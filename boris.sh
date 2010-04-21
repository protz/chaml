#!/bin/sh
x=1;
rm -f timings
max=9
echo -n "0/$max"
while [ $x -le $max ]; do
  echo -n "\r$x/$max";
  # Generate test file
  ocaml tests/test_boris.ml $x ocaml > boris.ml
  ocaml tests/test_boris.ml $x attapl > boris_attapl.ml
  ocaml tests/test_boris.ml $x mlf > boris_mlf.ml
  # Timings
  t1=0
  #t1=$(/usr/bin/time --format "%U" ocamlc.opt boris.ml 2>&1 > /dev/null)
  t2=0
  t2=$(/usr/bin/time --format "%U" ./chaml.native --dont-print-types boris.ml 2>&1 > /dev/null)
  t3=0
  #t3=$(/usr/bin/time --format "%U" mini boris_attapl.ml 2>&1 > /dev/null)
  t4=$(/usr/bin/time --format "%U" mlf < boris_mlf.ml 2>&1 > /dev/null)
  echo "$x,$t1,$t2,$t3,$t4" >> timings
  x=$(($x+1));
done;
rm -f boris.cm* boris*.ml
echo " ...done"
gnuplot script.gnuplot
eog timings.png
rm -f timings.png timings
