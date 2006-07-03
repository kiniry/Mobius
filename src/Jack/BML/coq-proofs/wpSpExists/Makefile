FILES= BasicDef.vo Logic_n.vo Language.vo Semantic.vo Wp_propag.vo Wp.vo axioms.vo helperTranslate.vo Translate.vo 




all: clean noclean
		
noclean: $(FILES)

%.vo : 
	coqc BasicDef
	coqc Logic_n
	coqc Language
	coqc Semantic	
	coqc Wp_propag	
	coqc Wp
	coqc axioms
	coqc helperTranslate
	coqc Translate




clean: 
	rm -f *.vo *~
