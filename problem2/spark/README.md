
Makefile entries:

* test: runs the program with assertions on the test provided in the problem description.
  check that the output is as expected.

* proof: runs GNATprove on the program, comparing the result with the stored proof_expected.out

------

Current status of proof:

* complete absence of RTE (see proof_expected.out), which requires also proving part of
  the functionality of Refine_One (see its postcondition)

* 5 assumptions used in code (pragma Assume):
   - 2 assumptions to account for the fact that Replace_Element on a map does not change
     its capacity. SPARK GPL 2014 does not allow proving it.
   - 2 assumptions logically equivalent to a proved assertion just above, one related to
     the use of 'Update and the other related to the relation between Contains and
     Has_Element on a vector. SPARK GPL 2014 does not allow proving them.
   - 1 assumption about the bounds of p.first + p.count, whose proof would require
     formalizing the counting of elements of X in the current partition p which have already
     been treated.

* proof of termination: there is a single non-for loop, whose termination is ensured by
  a loop variant which is proved
