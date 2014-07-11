
test:
	gprbuild -p -P patience
	bin/test_patience

proof:
	gnatprove -P patience --timeout=10 --report=all --proof=progressive --warnings=continue


clean:
	gnat clean -P patience
	gnatprove -P patience --clean
