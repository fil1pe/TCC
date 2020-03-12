all: compile

compile:
	@coqc DFA QSUtils

clear:
	@rm *.glob *.vo -f
