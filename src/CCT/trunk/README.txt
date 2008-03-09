CCT is a library for processing classes with certificates.

CCT can be built using ant. Following targets are available.
build - compile source files (class files are stored in build/)
dist  - create jar archive in dist/
tests.run - run JUnit tests.
tests.report - run tests and generate HTML report in tests/report
checkstyle - run checkstyle - report is stored in checkstyle-report/
clean - delete all generated files.

Default target is 'dist'.

CCT does not currently depend on any external library.
JUnit and checkstyle jars included in the distribution
are not necessary for using or building CCT.
