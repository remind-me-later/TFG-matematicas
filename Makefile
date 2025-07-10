.POSIX:

NAME=main
OUTDIR=build

all: $(OUTDIR)/$(NAME).pdf

$(OUTDIR)/$(NAME).pdf: src/$(NAME).tex
	latexmk -xelatex -output-directory=../$(OUTDIR) -shell-escape -cd -silent

$(OUTDIR):
	mkdir -p $(OUTDIR)

clean:
	$(RM) -r $(OUTDIR)

.PHONY: all clean