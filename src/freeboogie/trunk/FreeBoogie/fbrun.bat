SET ROOT=.
SET CP=%ROOT%/classes;%ROOT%/lib/antlr-2.7.7.jar;%ROOT%/lib/antlr-3.0.1.jar;%ROOT%/lib/stringtemplate-3.1b1.jar
java -Xms64m -Xmx64m -ea -cp "%CP%" %1 %2 %3 %4 %5 %6 %7 %8 %9

