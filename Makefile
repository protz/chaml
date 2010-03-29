PATH := /home/yquem/cristal/protzenk/Code/mini-trunk/trunk/src/:$(PATH)

all:
	ocamlbuild -I stdlib -I utils -I parsing chaml/chaml.native

debug:
	ocamlbuild -tag warn_A -tag warn_e -tag warn_z -tag debug -lflag -g -I stdlib -I utils -I parsing chaml/chaml.byte
	OCAMLRUNPARAM=b=1 ./chaml.byte \
		--print-constraint --pretty-printing --debug\
		--disable default-bindings test_chaml.ml 

print_constraint_mini:
	mini --do print-constraint test.ml

test_constraint_1:
	./chaml.native --print-constraint --pretty-printing test.ml
	./chaml.native --print-constraint test.ml --disable default-bindings --disable solver > _constraints
	mini --start parse-constraint _constraints

test_constraint_2:
	./chaml.native --print-constraint --disable generalize-match --pretty-printing test2.ml
	./chaml.native --print-constraint --disable generalize-match --disable solver --disable default-bindings test2.ml > _constraints
	mini --start parse-constraint _constraints

test_constraint_3:
	./chaml.native --print-constraint --pretty-printing test3.ml
	./chaml.native --print-constraint --disable solver --disable default-bindings test3.ml > _constraints
	mini --start parse-constraint _constraints

test_solve_compare:
	@printf '\x1b[38;5;204mMini output\x1b[38;5;15m\n'
	@mini test.ml
	@printf '\x1b[38;5;204mChaML output\x1b[38;5;15m\n'
	@./chaml.native test.ml

test_constraint_compare:
	@printf '\x1b[38;5;204mMini output\x1b[38;5;15m\n'
	@mini test.ml
	@printf '\x1b[38;5;204mChaML output\x1b[38;5;15m\n'
	@./chaml.native --print-constraint --disable default-bindings --disable solver test.ml > _constraints
	@mini --start parse-constraint _constraints

test_stdlib:
	cd stdlib && ocamlbuild jmap_test.native && ./jmap_test.native

clean:
	ocamlbuild -clean

count:
	wc -l `find chaml stdlib -iname '*.ml' -or -iname '*.mli'`
