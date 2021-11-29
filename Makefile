lp: lp.ml
	ocamlfind ocamlc -package angstrom -package stdio -linkpkg -g -o lp lp.ml
