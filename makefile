all: compile

compile:
	@coqc DFA QSUtils
	@coqc QueueingSystems
	@find . -name "*.vo.aux" -type f -delete

clear:
	@rm *.glob *.vo -f
