PATH := /home/yquem/cristal/protzenk/Code/mini-trunk/trunk/src/:$(PATH)

all:
	ocamlbuild -I stdlib -I utils -I parsing chaml/chaml.native

test: test_mini test_chaml

test_mini:
	mini --do print-constraint test.ml

test_chaml:
	./chaml.native --print-constraint --pretty-printing test.ml
	./chaml.native --print-constraint test.ml > _constraints
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
