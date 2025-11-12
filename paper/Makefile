# Makefile for Chebyshev Circles paper

# Main document name (without .tex extension)
MAIN = chebyshev_circles

# LaTeX compiler
LATEX = pdflatex
BIBTEX = bibtex

# Compilation flags
LATEXFLAGS = -interaction=nonstopmode -halt-on-error

.PHONY: all clean distclean view

# Default target: build the PDF
all: $(MAIN).pdf

# Full compilation with bibliography
$(MAIN).pdf: $(MAIN).tex references.bib
	$(LATEX) $(LATEXFLAGS) $(MAIN)
	$(BIBTEX) $(MAIN)
	$(LATEX) $(LATEXFLAGS) $(MAIN)
	$(LATEX) $(LATEXFLAGS) $(MAIN)

# Quick compilation (no bibliography update)
quick: $(MAIN).tex
	$(LATEX) $(LATEXFLAGS) $(MAIN)

# Clean auxiliary files
clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).bbl $(MAIN).blg $(MAIN).out $(MAIN).toc
	rm -f $(MAIN).fdb_latexmk $(MAIN).fls $(MAIN).synctex.gz

# Clean everything including PDF
distclean: clean
	rm -f $(MAIN).pdf

# View the PDF (macOS)
view: $(MAIN).pdf
	open $(MAIN).pdf

# Help message
help:
	@echo "Makefile for Chebyshev Circles paper"
	@echo ""
	@echo "Available targets:"
	@echo "  all        - Build the PDF (default)"
	@echo "  quick      - Quick compilation without bibliography update"
	@echo "  clean      - Remove auxiliary files"
	@echo "  distclean  - Remove all generated files including PDF"
	@echo "  view       - Open the PDF (macOS)"
	@echo "  help       - Show this help message"
