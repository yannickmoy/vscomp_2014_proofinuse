
test:
	gprbuild -p -P patience
	bin/test_patience

simple:
	gprbuild -p -P simple
	bin/simple

proof:
	gnatprove -P patience --timeout=5 --report=all --proof=progressive --warnings=continue

proofsimple:
	gnatprove -P simple --timeout=5 --report=all --proof=progressive --warnings=continue

clean:
	gnat clean -P patience
	gnatprove -P patience --clean
