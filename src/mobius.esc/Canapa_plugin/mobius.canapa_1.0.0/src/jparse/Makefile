## This is a makefile for JParse, the Java parser.  It may depend on
## features of GNU make.  If other makes fail, please send a bug report
## (and, better yet, a fix) to the JParse project maintainer: Jerry
## James <jamesj@acm.org>.

## JParse is free software; you can redistribute it and/or modify it
## under the terms of the GNU Lesser General Public License as published
## by the Free Software Foundation; either version 2.1, or (at your
## option) any later version.

## JParse is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
## License for more details.

## You should have received a copy of the GNU Lesser General Public
## License along with JParse; see the file COPYING.  If not, write to
## the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
## Boston, MA 02111-1307, USA.

## make           to build the class files for JParse
## make debug     to build a debugging version of the class files
## make jar       to create a JAR file containing the class files
## make doc       to create the Javadoc documentation for JParse
## make tags      to update the tags table
## make clean     to remove backup and autosave files
## make distclean to remove all files that can be created with this
##                makefile


######################### User configurable options ##########################

# The Java runtime to use (e.g., java, kaffe)
JAVA = java

# The Java compiler to use (e.g., javac, jikes, pizza)
JAVAC = javac

# Compilation flags.
ifdef DEBUG
JFLAGS = -g -source 1.4 -deprecation
else
JFLAGS = -O -source 1.4
endif

# The Java documentation generator to use
JAVADOC = javadoc

# Options to pass to the Java documentation generator
DOCFLAGS = -private -d ../doc -doctitle "JParse" -use -author \
-overview overview.html

# Tell javadoc where the standard Java class documentation resides
DOCLINK = -link file:/usr/java/j2sdk1.4.2_04/docs/api/
# DOCLINK = -link http://java.sun.com/j2se/1.4.2/docs/api/

# The Java archive creator to use
JAR = jar

# The TAGS creation program to use (e.g., ctags, etags)
TAGS = etags

###################### End of user configurable options ######################
################### Do not change anything below this line ###################

# Subdirectories that need to be made, too
SOURCEDIRS = expr stmt

# All of the files generated from java.g
JPARSER_SRC = JavaLexer.java JavaParser.java JavaTokenTypes.java
JPARSER_CLS = JavaLexer.class JavaParser.class JavaTokenTypes.class
JPARSER_TXT = JavaTokenTypes.txt

# All of the .class files
CLASS = CompileContext.class CompiledConstructor.class CompiledMethod.class \
	CompiledType.class ConstrAST.class Constructor.class FileAST.class \
	HasExceptions.class JavaAST.class LineReader.class MethAST.class \
	Method.class ModifierAST.class ParameterAST.class SourceType.class \
	SymbolTable.class Type.class TypeAST.class VarList.class

# All of the packages
PACKAGES = jparse jparse.expr jparse.stmt

# Pass variables down to submakes
.EXPORT_ALL_VARIABLES:

.PHONY:	all debug subdirs tags jar clean-norecurse clean distclean doc

all: $(JPARSER_CLS) $(CLASS) subdirs

debug:
	$(MAKE) all DEBUG=1

$(JPARSER_SRC): java.g
	$(JAVA) antlr.Tool java.g

%.class: %.java
	$(JAVAC) $(JFLAGS) $<

subdirs:
	for i in $(SOURCEDIRS); do \
		$(MAKE) -C $$i; \
	done

doc:
	$(JAVADOC) $(DOCFLAGS) $(DOCLINK) $(PACKAGES)

jar:	all
	cd ..; $(JAR) cf jparse.jar jparse

tags:
	find . -type f -name "*java" | $(TAGS) --members -

clean-norecurse:
	rm -f *~

clean: clean-norecurse
	for i in $(SOURCEDIRS); do \
		$(MAKE) -C $$i clean; \
	done

distclean: clean-norecurse
	rm -f TAGS $(JPARSER_SRC) $(JPARSER_TXT) *.class
	for i in $(SOURCEDIRS); do \
		$(MAKE) -C $$i distclean; \
	done
