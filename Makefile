PATH := /home/yquem/cristal/protzenk/Code/mini-trunk/trunk/src/:$(PATH)
BUILDFLAGS=-I stdlib -I utils -I parsing

.PHONY: tests

all:
	ocamlbuild $(BUILDFLAGS) chaml/chaml.native

debug:
	ocamlbuild -tag warn_A -tag warn_e -tag warn_z -tag debug \
	  $(BUILDFLAGS) chaml/chaml.byte
	OCAMLRUNPARAM=b=1 ./chaml.byte \
		--print-constraint --pretty-printing --debug\
		--disable default-bindings --disable generalize-match test.ml

tests:
	#ocamlbuild $(BUILDFLAGS) -I chaml -menhir "menhir --trace" tests/run_tests.byte chaml/chaml.native
	ocamlbuild $(BUILDFLAGS) -I chaml tests/run_tests.byte chaml/chaml.native
	./run_tests.byte

stdlib_tests:
	ocamlbuild stdlib/tests.native
	./tests.native

clean:
	ocamlbuild -clean

count:
	wc -l `find chaml stdlib -iname '*.ml' -or -iname '*.mli'` | sort -n

graph:
	ocamldoc -dot -I _build/chaml/ -I _build/parsing/ -I _build/stdlib/ \
	  -I _build/tests/ -I _build/utils/ chaml/*.ml -o graph.dot
	dot -Tpng graph.dot > graph.png
	eog graph.png
