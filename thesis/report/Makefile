LATEXCMD = pdflatex --shell-escape thesis.tex
BIBER = biber thesis

thesis:
	$(LATEXCMD) && $(BIBER) && $(LATEXCMD)

fast:
	$(LATEXCMD)

bibliography:
	$(BIBER)

clean:
	rm -rf *.aux *.bbl *.bcf *.blg *.lof *.log *.lot *.toc *.xml svg-inkscape *.pdf *.out *.lol
