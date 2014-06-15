vscomp_2014_proofinuse
======================

Submission to the VSComp 2014 competition (http://vscomp.org/)
from the 'ProofInUse' team

The team consists in:
- David Mentré (Mitsubishi Electric R&D Centre Europe)
- Claude Marché (Inria Saclay & LRI, CNRS, University Paris-Sud)
  mailto:Claude.Marche@inria.fr https://www.lri.fr/~marche/
- Yannick Moy (AdaCore)

We're using Why3 (https://why3.lri.fr/) and SPARK 2014
(http://www.spark-2014.org/) programming languages.








== Lessons learnt when using Why3 ==


= problem 1 =

* There should be a notation with brackets for lists

* It would be nice to have a List.forall higher-order predicate

* color highlighting of goals: color of premises and conclusion are
  wrong in presence of match..with

* missing lemmas on nth and append on lists (i.e. propagate lemmas in list.NthAppendLength to list.NthNoOpt)

* need for an abstract version of pigeon-hole lemma in Why3 stdlib,
  on functions instead of map like in map.MapInjection

* need for facilities to provide abstract specifications to Why3
  programs, and then provide raffinements (there is an on-going PhD
  thesis on that subject)

* "split" should really split match..with


