#
# The Extended BON Tool Suite
# Copyright (c) 2001-2002 Joseph Kiniry
# All Rights Reserved
#

#
# $Id: Makefile,v 1.2 2002/06/20 05:40:11 kiniry Exp $
#

all: index.txt BON_grammar.txt

%.txt: %.html
	lynx -dump $< > $(basename $<).txt
