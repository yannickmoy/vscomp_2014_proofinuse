
test:
	gprbuild -P partition_refinement
	./test_partition_refinement > test.out
	diff expected.out test.out

proof:
	gnatprove -P partition_refinement

clean:
	rm -f *~ test.out gnatinspect.*
	gnat clean -P partition_refinement
	gnatprove -P partition_refinement --clean
