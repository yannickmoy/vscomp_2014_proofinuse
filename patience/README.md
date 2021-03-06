# Why3 version of problem 1

## What is Why3 ?

Why3 is a platform for deductive program verification.
For more information see: http://why3.lri.fr/


## Makefile targets

* test: runs the test given in the task description

* prove: starts the proof IDE on the problem (using why3ide)

* replay: batch replay of all proofs (using why3replay)

* doc: produces the nicely formatted input code in ./patience.html

* dump: dumps the proof sessions in ./patience/why3session.html


## current status of development 

All developments are in file patience.mlw. The current proof status is
stored in the why3 session file patience/why3session.mlw, can be
edited using 'make prove', replayed using 'make replay' and dumped
into HTML using 'make dump'

It is recommended to read the pretty-printed documented code obtained
using 'make doc'

The file is made of 4 modules

* module PigeonHole

includes the pigeon-hole lemma. why3 stdlib already contains a similar
lemma map.MapInjection.injective_surjective, but cannot be used
directly because it talks about mappings instead of functions.  The
proof is done here using a lemma function and the recent improvements
of Why3 regarding higher-order logic.

*  module PatienceCode

includes a idiomatic code of the Patience game, operating on
lists. It is only annotated to prove its termination (using variants)
and also it is specified that stacks are non-empty, so as to prove
that the unreachable branch in the code (marked as
'absurd') is indeed unreachable.

* module PatienceAbstract

to specify and prove the properties required by the problem, it is
mandatory to keep track of a lot of informations regarding the
construction of the card stacks. this is done by introduction an
abstract state. An abstract code is then provided, operating on this
abstract state.  The two required properties are specified as
post-condition to the play_game procedure.  This are fully proved,
using the pigeon-hole lemma as expected for the second
property. Proofs only make use of automated provers: Alt-Ergo, CVC3
and Z3.

* module PatienceFull

this is a code that glues the idiomatic code and the abstract code,
the latter as ghost code. the main procedure play_game and the second
auxiliairy procedure play_cards are proved, but we could not achieve a
proof of the first auxiliairy procedure in the given time.






