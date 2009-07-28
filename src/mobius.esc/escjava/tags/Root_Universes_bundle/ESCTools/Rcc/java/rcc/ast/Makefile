# Copyright 2000, 2001, Compaq Computer Corporation

all:
	@echo "No all target exists!"

full: source
	javac -d ${CLASSDIRECTORY} *.java

#####

#
# Dependence on Javafe astgen programs:
#

ASTGEN = $(JAVAFE_ROOT)/astgen/astgen
ASTFILELIST = $(JAVAFE_ROOT)/astgen/astfilelist

$(ASTFILELIST) $(ASTGEN):
	(cd $(JAVAFE_ROOT)/astgen; ${MAKE})

#
# Generating Java files:
#

VECTEMPLATE = $(RCC_ROOT)/java/rcc/ast/_TYPE_Vec.j

TypeVec = Integer Substitution String ../tc/Instantiation\

IntegerVec.java: $(VECTEMPLATE)
	sed s/_TYPE_/Integer/g $(VECTEMPLATE) | \
        sed s/_PKG_/rcc.ast/g              | \
        sed s/_COMPONENTPKG_/java.lang/g > $@

StringVec.java: $(VECTEMPLATE)
	sed s/_TYPE_/String/g $(VECTEMPLATE) | \
        sed s/_PKG_/rcc.ast/g              | \
        sed s/_COMPONENTPKG_/java.lang/g > $@


SubstitutionVec.java: $(VECTEMPLATE)
	sed s/_TYPE_/Substitution/g $(VECTEMPLATE) | \
        sed s/_PKG_/rcc.ast/g              | \
        sed s/_COMPONENTPKG_/rcc.ast/g > $@


../tc/InstantiationVec.java: $(VECTEMPLATE)
	sed s/_TYPE_/Instantiation/g $(VECTEMPLATE) | \
        sed s/_PKG_/rcc.tc/g              | \
        sed s/_COMPONENTPKG_/rcc.tc/g > ../tc/$@


source: GeneratedTags.java  $(ASTGEN) ../tc/InstantiationVec.java IntegerVec.java SubstitutionVec.java StringVec.java

GeneratedTags.java: $(ASTGEN) hierarchy.j
	$(ASTGEN) < hierarchy.j

#####

clean: $(ASTFILELIST)
	$(ASTFILELIST) < hierarchy.j | xargs rm -f 
	rm -f *~ ../tc/InstantiationVec.java IntegerVec.java \
                 SubstitutionVec.java StringVec.java ASTGEN* zASTGEN* *.tmp
	rm -rf *.class ${CLASSDIRECTORY}/rcc/ast/*.class

runtest:
	@echo "No tests to run."
