SRC := paper.tex \
       related.tex \
       conclusions.tex \
       paper.bib

AGDA := /home/tema/.local/bin/agda
I := /home/tema/src/agda-stdlib-experimental/src

all: paper.pdf


.PHONY: paper.tex
paper.tex : latex/background.tex latex/kaleidoskope.tex latex/arraylang.tex \
	    latex/aplcnn.tex

latex/%.tex : %.lagda
	$(AGDA) --include-path=$(I) --latex $< #--only-scope-checking $<

paper.pdf: $(SRC)
	TEXINPUTS=./latex:$$TEXINPUTS latexmk -pdf -f -pdflatex='xelatex -halt-on-error' $<

clean:
	$(RM) *.aux *.log *.out *.vrb paper.pdf \
              *.bbl *.blg *.fdb_latexmk *.toc *.fls *.cut \
              latex/*.tex latex/*.aux *.agdai

