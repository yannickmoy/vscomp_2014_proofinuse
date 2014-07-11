
test:
	gprbuild -p -P simple
	bin/simple

proof:
	gnatprove -P simple --timeout=5 --report=all --proof=progressive --warnings=continue

clean:
	gnat clean -P simple
	gnatprove -P simple --clean
