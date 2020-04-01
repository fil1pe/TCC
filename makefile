all: compile

compile:
	@coqc DFA
	@coqc QS
	@find . -name "*.vo.aux" -type f -delete
	@find . -name "*.glob" -type f -delete
	@find . -name "*.vok" -type f -delete
	@find . -name "*.vos" -type f -delete

clear:
	@rm *.glob *.vo -f
