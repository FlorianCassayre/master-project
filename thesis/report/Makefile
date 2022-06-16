LATEXCMD = pdflatex --shell-escape thesis.tex
BIBER = biber thesis

fast:
	$(LATEXCMD)

thesis:
	$(LATEXCMD) && $(BIBER) && $(LATEXCMD)

bibliography:
	$(BIBER)

clean:
	rm -rf *.aux *.bbl *.bcf *.blg *.lof *.log *.lot *.toc *.xml svg-inkscape *.pdf
