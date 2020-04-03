all: compile_bib compile

compile_bib:
	@pdflatex --shell-escape TCC.tex
	@bibtex TCC
	@pdflatex --shell-escape TCC.tex

compile:
	@pdflatex --shell-escape TCC.tex
	@find . -name "*.dvi" -type f -delete
	@find . -name "*.lof" -type f -delete
	@find . -name "*.log" -type f -delete
	@find . -name "*.loq" -type f -delete
	@find . -name "*.out.ps" -type f -delete
	@find . -name "*.toc" -type f -delete
	@find . -name "*.blg" -type f -delete
	@rm -r _minted-TCC
