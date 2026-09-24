.DEFAULT_GOAL := all

LATEXMK := latexmk
LATEX_FLAGS := -pdf -interaction=nonstopmode -halt-on-error
MANUSCRIPT_DIR := Article
ARCHIVE_DIR := Article/archive
ARTICLE := schrodinger_phase_retrieval_results.tex
STATIONARY := schrodinger_phase_retrieval_stationary_results.tex

.PHONY: all article stationary clean

all: article stationary

article:
	cd $(MANUSCRIPT_DIR) && $(LATEXMK) $(LATEX_FLAGS) $(ARTICLE)

stationary:
	cd $(ARCHIVE_DIR) && $(LATEXMK) $(LATEX_FLAGS) $(STATIONARY)

clean:
	cd $(MANUSCRIPT_DIR) && $(LATEXMK) -C $(ARTICLE)
	cd $(ARCHIVE_DIR) && $(LATEXMK) -C $(STATIONARY)
