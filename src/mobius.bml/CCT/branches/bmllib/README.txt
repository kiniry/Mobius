CCT = Class Certificate Transformer = framework
for verifying and manipulating certificates.

CCT can be built using ant. Following targets are available.
build - compile source files (class files are stored in build/)
dist  - create jar archive in dist/
doc - create javadocs in apidocs/
tests.run - run JUnit tests.
tests.report - run tests and generate HTML report in tests/report
checkstyle - run checkstyle - report is stored in checkstyle-report/
clean - delete all generated files.

Default target is 'dist'.

CCT does not currently depend on any external libraries.
JUnit and checkstyle jars included in the repository
are not necessary for using or building CCT.

Simple command line tools can be accessed by calling
main method in mobius.cct.tools.Main or by executing
the jar file created by 'ant dist'.
