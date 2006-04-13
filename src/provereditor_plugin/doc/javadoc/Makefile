
PROVER_EDITOR_DIR="../ProverEditor"
COQ_EDITOR_DIR="../CoqEditor"
COQ_SUGAR_DIR="../CoqEclipseSugar"
JAVA_LNK=-link http://java.sun.com/j2se/1.4.2/docs/api/
ECLI_LNK=-link http://help.eclipse.org/help31/

all:
	javadoc ${ECLI_LNK} ${JAVA_LNK} `find ../${PROVER_EDITOR_DIR} -name "*.java"` `find ../${COQ_EDITOR_DIR} -name "*.java"` `find ../${COQ_SUGAR_DIR} -name "*.java"`