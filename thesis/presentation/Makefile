LATEXCMD = pdflatex --shell-escape

define generate_thumbnail
	pdftoppm -f $(1) -l $(1) -r 50 ../report/thesis.pdf -png thumbnail
	optipng -o7 thumbnail-$(1).png
	mv thumbnail-$(1).png figures/
endef

define make_presentation_fast
	BEAMERMODE=$(1) $(LATEXCMD) -jobname=presentation-$(1) presentation.tex
endef

define make_presentation
	$(call make_presentation_fast,$(1))
	$(call make_presentation_fast,$(1))
endef

thesis:
	$(call make_presentation,slides-only)
	$(call make_presentation,slides-notes-interlaced)
	$(call make_presentation,slides-notes-dual)

fast:
	$(call make_presentation_fast,slides-only)

generate-thumbnails:
	cd ../report && $(MAKE) && cd ../presentation
	$(call generate_thumbnail,01)
	$(call generate_thumbnail,08)
	$(call generate_thumbnail,10)
	$(call generate_thumbnail,29)
	$(call generate_thumbnail,39)

clean:
	rm -rf *.aux *.bbl *.bcf *.blg *.lof *.log *.lot *.toc *.xml svg-inkscape *.pdf *.nav *.out *.snm *.vrb
