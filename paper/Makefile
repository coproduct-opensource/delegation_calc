# Paper build Makefile.
# `make pdf` produces main.pdf. Requires latexmk + acmart.cls.

.PHONY: pdf clean watch

pdf:
	latexmk -pdf -interaction=nonstopmode main.tex

watch:
	latexmk -pdf -pvc -interaction=nonstopmode main.tex

clean:
	latexmk -c
	rm -f main.pdf main.bbl main.run.xml
