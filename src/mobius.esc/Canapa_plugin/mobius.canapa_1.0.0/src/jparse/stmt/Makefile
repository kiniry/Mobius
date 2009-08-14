# This is a makefile for jparse.stmt, the statement subpackage of the Java
# compiler skeleton.  It may depend on features of GNU make.  If other
# makes fail, please send a bug report (and, better yet, a fix) to the
# JParse project maintainer: Jerry James <jamesj@acm.org>.

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

###################### End of user configurable options ######################
################### Do not change anything below this line ###################

# All of the .class files
CLASS = BreakAST.class CaseGroupAST.class CatchAST.class ClassAST.class \
	CompoundAST.class ContinueAST.class DeclarationAST.class \
	DoWhileAST.class EmptyAST.class ExpressionAST.class ForAST.class \
	IfElseAST.class LabelAST.class ReturnAST.class StatementAST.class \
	SwitchAST.class SynchronizedAST.class ThrowAST.class TryAST.class \
	WhileAST.class

.PHONY:	all debug clean distclean

all: $(CLASS)

debug:
	$(MAKE) all DEBUG=1

%.class: %.java
	$(JAVAC) $(JFLAGS) $<

clean:
	rm -f *~

distclean: clean
	rm -f *.class
