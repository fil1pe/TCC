all: compile

compile:
	@coqc DFA QSUtils
	@find . -name "*.vo.aux" -type f -delete

clear:
	@rm *.glob *.vo -f
