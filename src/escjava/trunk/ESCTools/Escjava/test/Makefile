all:
	cd escjava/parser/test; ${MAKE}

runtest:
	cd escjava/parser/test; ${MAKE} runtest
	cd escjava/test; ${MAKE} runtest

bigtest:
	cd matrix; escjava \*.java

source:
	@echo "ERROR: this is not a legal target!"

class:
	@echo "ERROR: this is not a legal target!"

clean: 
	rm -rf *.class *~
