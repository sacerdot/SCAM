all: strong_cbv

strong_cbv: strong_cbv.ml
	ocamlopt -o strong_cbv strong_cbv.ml

.PHONY: all
