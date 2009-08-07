DOXYGEN=
# DOXYTAG=

FIG=theory_api_flow.fig
JPG=$(patsubst %.fig, %.jpg, $(FIG))
EPS=$(patsubst %.fig, %.eps, $(FIG))

all: doc

doc: $(JPG) $(EPS)
ifdef DOXYGEN
	$(DOXYGEN) Doxyfile
# ifdef DOXYTAG
# 	cd html; $(DOXYTAG) -s search.idx
# endif
else
	@echo "doxygen is not configured; no documentation will be generated"
endif

%.jpg: %.fig
	 -L jpeg $< $@
%.eps: %.fig
	 -L eps $< $@

install:
	@echo "Sorry, Docs installation is not implemented yet"

distclean:
	@rm -f Doxyfile *.eps *.jpg Makefile
	@rm -rf html
