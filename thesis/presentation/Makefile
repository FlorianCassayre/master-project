LATEXCMD = pdflatex --shell-escape presentation.tex

fast:
	$(LATEXCMD)

thesis:
	$(LATEXCMD) && $(LATEXCMD)

clean:
	rm -rf *.aux *.bbl *.bcf *.blg *.lof *.log *.lot *.toc *.xml svg-inkscape *.pdf
