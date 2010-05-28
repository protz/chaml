PATH := /home/yquem/cristal/protzenk/Code/mini-trunk/trunk/src/:$(PATH)
BUILDFLAGS=-I stdlib -I utils -I parsing -I pprint -cflag -strict-sequence

.PHONY: tests doc

all:
	./yacchack.sh
	ocamlbuild $(BUILDFLAGS) chaml/chaml.native
	./noyacchack.sh

profiling:
	./yacchack.sh
	ocamlbuild $(BUILDFLAGS) -tag debug chaml/chaml.native
	./noyacchack.sh
	valgrind --tool=callgrind ./chaml.native --dont-print-types test.ml
	kcachegrind callgrind.out.*
	rm -f callgrind.out.*

debug:
	./yacchack.sh
	ocamlbuild -tag debug \
	  $(BUILDFLAGS) -tag use_unix chaml/chaml.byte
	OCAMLRUNPARAM=b=1 ./chaml.byte \
		--print-constraint --enable pretty-printing --enable debug\
		--disable default-bindings\
		--enable recursive-types\
		test.ml
	./noyacchack.sh

debug_ast:
	./yacchack.sh
	ocamlbuild -tag debug \
	  $(BUILDFLAGS) -tag use_unix chaml/chaml.byte
	OCAMLRUNPARAM=b=1 ./chaml.byte --print-typed-ast --enable debug \
		--print-core-ast\
		test.ml
	./noyacchack.sh

tests:
	./yacchack.sh
	#ocamlbuild $(BUILDFLAGS) -I chaml -menhir "menhir --trace" tests/run_tests.byte chaml/chaml.native
	ocamlbuild $(BUILDFLAGS) -I chaml tests/run_tests.byte chaml/chaml.native
	./run_tests.byte
	./noyacchack.sh

stdlib_tests:
	ocamlbuild stdlib/tests.native
	./tests.native

clean:
	ocamlbuild -clean

count:
	#wc -l `find chaml stdlib tests -iname '*.ml' -or -iname '*.mli' -or -iname '*.mly' -or -iname '*.mll'` | sort -n
	sloccount chaml tests stdlib Makefile *.sh

GRAPH_FILES = $(shell find chaml -iname '*.ml*' -and -not -iname 'algebra.ml*' -and -not -iname '.*' -and -not -iname 'algebra.ml*' -and -not -iname 'typePrinter.ml*')
#GRAPH_FILES = $(shell ls chaml/*.ml*)
#GRAPH_FILES = $(shell ls chaml/*.ml* stdlib/*.ml*)

build_graph:
	ocamldoc -dot -I _build/chaml/ -I _build/parsing/ -I _build/stdlib/ \
	  -I _build/tests/ -I _build/utils/ -I _build/pprint \
	  -I $(shell ocamlbuild -where)\
	  $(GRAPH_FILES)\
	  -o graph.dot
	dot -Tpng graph.dot > graph.png
	convert graph.png -rotate 90 graph.png
	rm -f graph.dot

graph: build_graph
	eog graph.png

OCAMLLIBPATH = $(shell ocamlc -where)

#DOCFILES = $(shell find chaml stdlib -iname '*.ml' -or -iname '*.mli') #`find $(OCAMLLIBPATH) -maxdepth 1 -iname '*.mli' -and -not -iname 'condition.mli'`
DOCFILES = chaml/constraint.mli chaml/oCamlConstraintGenerator.mli\
	   chaml/unify.mli chaml/mark.mli\
	   chaml/solver.mli chaml/camlX.mli chaml/infiniteArray.mli\
	   chaml/algebra.mli chaml/unionFind.mli\
	   chaml/typePrinter.mli chaml/translator.mli\
	   chaml/core.mli chaml/desugar.mli chaml/atom.mli\
	   chaml/deBruijn.mli pprint/pprint.mli\
	   stdlib/*.mli #`find $(OCAMLLIBPATH) -maxdepth 1 -iname '*.mli' -and -not -iname 'condition.mli'`

doc: build_graph
	mkdir -p doc
	ocamldoc -html -I _build/chaml/ -I _build/parsing/ -I _build/stdlib/ \
	  -I _build/tests/ -I _build/utils/ -I _build/pprint \
	  -I `ocamlc -where` -d doc \
	  -intro doc/main $(DOCFILES)
	sed -i 's/iso-8859-1/utf-8/g' doc/*.html
	sed -i 's/<\/body>/<img src="..\/graph.png" \/><\/body>/' doc/index.html
	cp -f ocamlstyle.css doc/style.css
