all: compile

compile:
	@coqc Utils
	@coqc DFA
	@coqc QS
	@find . -maxdepth 1 -name "*.vo.aux" -type f -delete
	@find . -maxdepth 1 -name "*.glob" -type f -delete
	@find . -maxdepth 1 -name "*.vok" -type f -delete
	@find . -maxdepth 1 -name "*.vos" -type f -delete

clear:
	@rm *.glob *.vo -f
