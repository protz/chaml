PATH := /home/yquem/cristal/protzenk/Code/yrg-mini-prototype-0.2/src/:$(PATH)

all:
	ocamlbuild -I stdlib -I utils -I parsing chaml/chaml.native

test:
	mini --do print-constraint test.ml
	./chaml.native --print-constraint test.ml > _constraints
	@cat _constraints
	mini --start parse-constraint _constraints

unit_test:
	cd stdlib && ocamlbuild jmap_test.native && ./jmap_test.native

bug_mini1:
	mini --end print-constraint bug_mini1.ml > _constraint_mini
	@cat _constraint_mini
	mini --start parse-constraint _constraint_mini

bug_mini2:
	mini --end print-constraint bug_mini2.ml > _constraint_mini
	@cat _constraint_mini
	mini --start parse-constraint _constraint_mini
