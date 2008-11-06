In order to compile BmlLib one must have BCEL 5.1 plugin which is located at
svn+ssh://scm.gforge.inria.fr/svn/mobius/WP3/Task_3.6_Program_Verification_Environment/libs/bcel-5.1
and generate parser from ANTLR source in 
BmlLib/src/annot/textio/BML.g3
an Eclipse plugin which generates the Java parser from g3 file is located
at http://javadude.com/eclipse/update.

More information in Bmllib/src/txt/readme.txt


How to generate java files from .g3 file (in my local directories):
In src do:
JAVA=<path to Java SDK>
$JAVA/bin/java -Xmx1024m -cp $JAVA/jre/lib/rt.jar:../lib/stringtemplate-3.1b1.jar:../lib/antlr-3.0.1.jar:../lib/antlr-2.7.7.jar org.antlr.Tool -o ../antlr3-generated annot/textio/BML.g3
