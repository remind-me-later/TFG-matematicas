.POSIX:

name=tfg_mates
sources:=$(shell find src -maxdepth 2 -name '*.tex')
style:=$(shell find sty -name '*.sty')
makefiles:=$(shell find . -mindepth 1 -maxdepth 4 -type f -name Makefile)
subdir:=$(filter-out ./,$(dir $(makefiles)))

OUTDIR=build

all: $(OUTDIR)/$(name).pdf

$(OUTDIR)/$(name).pdf: $(sources) $(style) | $(OUTDIR)
	latexmk -xelatex -output-directory=../$(OUTDIR) -cd -silent --shell-escape

$(OUTDIR):
	mkdir -p $(OUTDIR)

clean:
	for dir in $(subdir); do \
		make -C $$dir clean; \
	done
	$(RM) -r $(OUTDIR)

cle:
	$(RM) -r $(OUTDIR)

.PHONY: all clean cle
