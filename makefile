all:
	@coqc NatListSet.v
	@coqc Pigeonhole.v
	@coqc Digraph.v
	@coqc DFA.v
	@coqc DFA_Digraph.v
	@coqc ReachableState.v
	@coqc DistinguishableStates.v
	@coqc Equivalent_DFAs.v
	@rm *.glob *.vok *.vos .*.aux .nia.cache

clean:
	@rm *.vo

