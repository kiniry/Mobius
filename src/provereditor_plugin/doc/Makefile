
PROVER_EDITOR_DIR=../ProverEditor
COQ_EDITOR_DIR=../CoqEditor
COQ_SUGAR_DIR=../CoqEclipseSugar
JAVA_LNK=-link http://java.sun.com/j2se/1.4.2/docs/api/
ECLI_LNK=-link http://mobius.inria.fr/eclipse-doc/
CLASS=`find ~/eclipse/plugins/ -name "*.jar" | tr '\n' ':'`
all:
	cd javadoc ;\
	find ../${PROVER_EDITOR_DIR} -name "*.java" > files; \
	find ../${COQ_SUGAR_DIR} -name "*.java" >> files; \
	find ../${COQ_EDITOR_DIR} -name "*.java" >> files; \	
	javadoc ${ECLI_LNK} ${JAVA_LNK}  -classpath ${CLASS} @files 

clean:
	rm -rf javadoc; mkdir javadoc
