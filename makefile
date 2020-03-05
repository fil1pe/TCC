all: compile

compile:
	@coqc DFA Utils

clear:
	@rm *.glob *.vo
