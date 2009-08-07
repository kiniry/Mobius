##################################################
# About this Makefile
#
# This Makefile depends on Makefile.opts
##################################################

MODULE = cvc3

SRC =   main.cpp

EXECUTABLE = $(PROJECTNAME)

EXTRAFLAGS = -DVERSION=\"$(VERSION)\"

LD_LIBS = -l$(PROJECTNAME)

OTHER_DEPENDENCIES = $(TOP)/lib/$(PLATFORM_WITH_OPTIONS)/lib$(PROJECTNAME).$(LIB_SUFFIX)

include ../../Makefile.local
