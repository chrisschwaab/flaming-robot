N=effects

all: $N.dvi
pdf: $N.pdf

clean:
	rm -rf generated/

distclean: clean
	rm -f $N.pdf $N.ps $N.dvi

#%.fmt: %.lhs
#	lhs2TeX-hl -o $@ $<

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

.PHONY: all pdf clean distclean
