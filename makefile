all: compile bib
	@pdflatex tcc.tex -shell-escape

compile:
	@pdflatex tcc.tex -shell-escape

bib:
	@bibtex tcc