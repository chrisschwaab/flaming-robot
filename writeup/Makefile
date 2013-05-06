N=effects

#all: $N.pdf
all: $N.dvi

clean:
	rm -rf generated/

distclean: clean
	rm -f $N.pdf $N.ps $N.dvi

%.tex: %.lhs
	@mkdir -p generated
	lhs2TeX $< -o generated/$@

%.dvi %.aux: %.tex
	latex -output-directory=generated generated/$<

%.ps: %.dvi
	dvips -P pdf -t letter -o $(basename $<).ps generated/$<

#%.bbl: %.aux
#	@cp -f refs.bib generated/
#	cd generated && biber $(basename $<)

%.pdf: %.tex
	pdflatex -output-dir=generated generated/$<
	cp generated/$(basename $<).pdf $(basename $<).pdf

.PHONY: all clean distclean
