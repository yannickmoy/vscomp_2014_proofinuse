
test:
	gprbuild -p -P patience
	bin/test_patience 
	# > test.out
	# diff test_expected.out test.out

proof:
	gnatprove -P patience --timeout=5 --report=all --proof=progressive 
	# > proof.out
	# diff proof_expected.out proof.out

clean:
	gnat clean -P patience
	gnatprove -P patience --clean
	#rm -f *~ test.out proof.out gnatinspect.*
