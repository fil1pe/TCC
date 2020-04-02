all: compile_bib compile

compile_bib:
	@latex --shell-escape TCC.tex
	@bibtex TCC
	@latex --shell-escape TCC.tex

compile:
	@latex --shell-escape TCC.tex
	@dvipdfm TCC
	@find . -name "*.dvi" -type f -delete
	@find . -name "*.lof" -type f -delete
	@find . -name "*.log" -type f -delete
	@find . -name "*.loq" -type f -delete
	@find . -name "*.out.ps" -type f -delete
	@find . -name "*.toc" -type f -delete
	@find . -name "*.blg" -type f -delete
	@rm -r _minted-TCC
