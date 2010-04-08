PATH := /home/yquem/cristal/protzenk/Code/mini-trunk/trunk/src/:$(PATH)
BUILDFLAGS=-I stdlib -I utils -I parsing -cflag -strict-sequence

.PHONY: tests doc

all:
	ocamlbuild $(BUILDFLAGS) chaml/chaml.native

debug:
	ocamlbuild -tag warn_A -tag warn_e -tag warn_z -tag debug \
	  $(BUILDFLAGS) -tag use_unix chaml/chaml.byte
	OCAMLRUNPARAM=b=1 ./chaml.byte \
		--print-constraint --enable pretty-printing --enable debug\
		--disable default-bindings test.ml

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
	wc -l `find chaml stdlib tests -iname '*.ml' -or -iname '*.mli' -or -iname '*.mly' -or -iname '*.mll'` | sort -n

build_graph:
	ocamldoc -dot -I _build/chaml/ -I _build/parsing/ -I _build/stdlib/ \
	  -I _build/tests/ -I _build/utils/ chaml/*.ml -o graph.dot
	dot -Tpng graph.dot > graph.png
	convert graph.png -rotate 90 graph.png

graph: build_graph
	eog graph.png

OCAMLLIBPATH = $(shell ocamlc -where)

DOCFILES = chaml/oCamlConstraintGenerator.mli chaml/constraint.mli chaml/unify.mli\
	   chaml/solver.mli\
	   chaml/algebra.mli chaml/unionFind.mli\
	   chaml/typePrinter.mli\
	   stdlib/*.mli #`find $(OCAMLLIBPATH) -maxdepth 1 -iname '*.mli' -and -not -iname 'condition.mli'`

doc: build_graph
	mkdir -p doc
	ocamldoc -html -I _build/chaml/ -I _build/parsing/ -I _build/stdlib/ \
	  -I _build/tests/ -I _build/utils/ -I `ocamlc -where` -d doc \
	  -intro doc/main $(DOCFILES)
	sed -i 's/iso-8859-1/utf-8/g' doc/*.html
	sed -i 's/<\/body>/<img src="..\/graph.png" \/><\/body>/' doc/index.html
	cp -f ocamlstyle.css doc/style.css
