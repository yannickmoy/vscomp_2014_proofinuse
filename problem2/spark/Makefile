
test:
	gprbuild -p -P partition_refinement
	bin/test_partition_refinement > test.out
	diff expected.out test.out

proof:
	gnatprove -p -P partition_refinement

clean:
	gnat clean -P partition_refinement
	gnatprove -P partition_refinement --clean
	rm -f *~ test.out gnatinspect.*
	rm -rf bin obj
