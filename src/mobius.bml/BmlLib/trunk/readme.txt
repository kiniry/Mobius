In order to compile BmlLib one must 
* have BCEL 5.2 plugin which is located at
https://mobius.ucd.ie/repos/libs/bcel-5.2

and 
* generate parser from ANTLR source in 
BmlLib/src/annot/textio/BML.g3

To do that, cd to src and:
JAVA=<path to Java SDK>
$JAVA/bin/java -Xmx1024m -cp $JAVA/jre/lib/rt.jar:../lib/stringtemplate-3.1b1.jar:../lib/antlr-3.0.1.jar:../lib/antlr-2.7.7.jar org.antlr.Tool -o ../antlr3-generated annot/textio/BML.g3

Alternatively, you can ant build_grammar.xml



More information in BmlLib/src/txt/readme.txt

