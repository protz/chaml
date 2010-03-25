PATH := /home/yquem/cristal/protzenk/Code/mini-trunk/trunk/src/:$(PATH)

all:
	ocamlbuild -I stdlib -I utils -I parsing chaml/chaml.native

debug:
	ocamlbuild -cflag -g -lflag -g -I stdlib -I utils -I parsing chaml/chaml.byte
	OCAMLRUNPARAM=b=1 ./chaml.byte --print-constraint --pretty-printing --debug test_chaml.ml 

test: test_mini test_chaml

test_mini:
	mini --do print-constraint test.ml

test_chaml:
	./chaml.native --print-constraint --pretty-printing test.ml
	./chaml.native --print-constraint test.ml > _constraints
	mini --start parse-constraint _constraints

test_chaml2:
	./chaml.native --print-constraint --disable generalize-match --pretty-printing test2.ml
	./chaml.native --print-constraint --disable generalize-match test2.ml > _constraints
	mini --start parse-constraint _constraints

test_chaml3:
	./chaml.native --print-constraint --pretty-printing test3.ml
	./chaml.native --print-constraint test3.ml > _constraints
	mini --start parse-constraint _constraints

test_compare:
	@printf '\x1b[38;5;204mMini output\x1b[38;5;15m\n'
	@mini test.ml
	@printf '\x1b[38;5;204mChaML output\x1b[38;5;15m\n'
	@./chaml.native --print-constraint test.ml > _constraints
	@mini --start parse-constraint _constraints

test_stdlib:
	cd stdlib && ocamlbuild jmap_test.native && ./jmap_test.native

clean:
	ocamlbuild -clean

count:
	wc -l `find . -iname '*.ml' -iname '*.mli'`
