.PHONY: clean compile_w compile_w32

clean:
	-rm *~ *.cmo *.cmi *.cmx *.o mcparser.mli mcparser.ml mclexer.ml *.bak *.obj

slmc: namegen.mli piastnode.mli ccastnode.mli equations.mli process.mli iterator.mli formastnode.mli mcmenu.mli checker.mli
	ocamllex mclexer.mll
	ocamlyacc mcparser.mly
	ocamlc -c namegen.mli piastnode.mli ccastnode.mli equations.mli process.mli iterator.mli formastnode.mli mcmenu.mli checker.mli
	ocamlc -o slmc namegen.ml piastnode.ml ccastnode.ml equations.ml process.ml iterator.ml formastnode.ml checker.ml mclexer.ml mcparser.ml mcmain.ml

sl-mc_w.exe: slmc
	cp slmc sl-mc_w.exe

sl-mc_w32.exe: slmc
	cp slmc sl-mc_w32.exe

compile_w: sl-mc_w.exe

compile_w32: sl-mc_w32.exe