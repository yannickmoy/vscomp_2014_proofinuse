
test:
	gprbuild -p -P partition_refinement
	bin/test_partition_refinement > test.out
	diff test_expected.out test.out

proof:
	gnatprove -P partition_refinement --timeout=120 -q --report=all > proof.out
	diff proof_expected.out proof.out

clean:
	gnat clean -P partition_refinement
	gnatprove -P partition_refinement --clean
	rm -f *~ test.out proof.out gnatinspect.*
	rm -rf bin obj
