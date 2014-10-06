default : CS410.pdf

CS410.tex : CS410.lagda Introduction.lagda BasicPrelude.lagda EmacsCheatSheet.lagda Logic.lagda Razor.lagda
	lhs2TeX --agda CS410.lagda > CS410.tex

CS410.aux : CS410.tex
	latex CS410

CS410.blg : CS410.aux CS410.bib
	bibtex CS410

CS410.dvi : CS410.tex CS410.blg
	latex CS410
	latex CS410

CS410.pdf : CS410.tex CS410.blg
	pdflatex CS410


# Ex2

EX2=Ex2
REPLACE=replace

ex2: $(EX2).pdf

$(EX2).pdf: latex/$(EX2).tex
	cd latex/ && \
	latexmk -pdf -use-make $(EX2).tex && \
	mv $(EX2).pdf ..

latex/%.tex: %.lagda
	agda --allow-unsolved-metas -i . --latex $<
	sed -f $(REPLACE).sed $@ > $@.sedded
	mv $@.sedded $@