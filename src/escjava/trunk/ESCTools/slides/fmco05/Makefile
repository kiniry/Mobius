# @(#)$Id$

# Copyright (C) 2006 Iowa State University

# This file is part of JML

# JML is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.

# JML is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with JML; see the file COPYING.  If not, write to
# the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

include Makefile.defs

JAVAC = javac
JAVACFLAGS = 
JML = jml
JMLC = jmlc
JMLCFLAGS = -Q -a
JMLUNIT = jmlunit
JAVA = java
JMLRAC = jmlrac
TEXCMDPRE = export TEXINPUTS="$(TEXINPUTS)"
LATEX = $(TEXCMDPRE); latex
PDFLATEX = $(TEXCMDPRE); pdflatex
BIBTEX = bibtex

paper =		fmco

sourcefiles =	TickTockClock.java	\
		SettableClock.java	\
		Clock.java		\
		AlarmClock_interfaceless.java \

#		AlarmClock.java

texfiles =	$(addsuffix .tex,$(paper))

dvifiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.dvi,$(texfile)))

psfiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.ps,$(texfile)))

pdffiles =	$(foreach texfile,$(texfiles),\
		$(subst .tex,.pdf,$(texfile)))

classfiles =	$(foreach sourcefile,$(sourcefiles),\
		$(subst .java,.class,$(sourcefile)))

.PHONY: all paper source typecheck

all:	paper source

paper:  $(dvifiles) $(psfiles) $(pdffiles)
source: $(classfiles)

%.pdf: %.tex
	pdflatex $< $@

%.pdf.gz: %.pdf
	gzip -c $< > $@

%.ps: %.dvi
	dvips -Pcmz -Pamz -f < $< > $@

%.ps.gz: %.ps
	gzip -c $< > $@

# %.class: %.java
# 	$(JAVAC) $(JAVAFLAGS) $<

${paper}.dvi: ${sourcefiles} ${paper}.tex
	$(LATEX) ${paper}; $(LATEX) ${paper}; $(BIBTEX) ${paper}; \
	$(LATEX) ${paper}; $(LATEX) ${paper};

${paper}.pdf: ${sourcefiles} ${paper}.tex
	$(PDFLATEX) ${paper}; $(PDFLATEX) ${paper}; $(BIBTEX) ${paper}; \
	$(PDFLATEX) ${paper}; $(PDFLATEX) ${paper};


%.class: %.java
	$(JMLC) $(JMLCFLAGS) $<

check:
	$(JML) -Q $(sourcefiles)

javac:
	javac $(sourcefiles)
	mjc2 DigitalDisplayClock.java

clean cleanup:
jml:
	$(JML) -Q $(sourcefiles)
	$(JML) -Q --universes DigitalDisplayClock.java

clean cleanup:
	rm -f _region_* *.aux *.log *.blg *.class \
		${paper}.dvi ${paper}.ps ${paper}.pdf jmllogo.pdf

pristine cleanall: clean
	rm -rf `cat .cvsignore`

info:
	@echo "CLASSPATH=" $$CLASSPATH
	@echo "JMLHOME=" $$JMLHOME

# End of file
