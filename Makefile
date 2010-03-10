PATH := /home/yquem/cristal/protzenk/Code/yrg-mini-prototype-0.2/src/:$(PATH)

all:
	ocamlbuild -I stdlib -I utils -I parsing chaml/chaml.native

test:
	mini --do print-constraint test.ml
	./chaml.native --print-constraints test.ml > _constraints
	@cat _constraints
	mini --start parse-constraint _constraints
