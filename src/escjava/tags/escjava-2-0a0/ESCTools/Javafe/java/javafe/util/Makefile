# Copyright 2000, 2001, Compaq Computer Corporation

runtest:
	${JAVA} javafe.util.CorrelatedReaderTest subreader <CorrelatedReader.java
	${JAVA} javafe.util.CorrelatedReaderTest reset <CorrelatedReader.java


	#
	# below tests removed because they exceeds CorrelatedReaderTest max
	# file size:
	#${JAVA} javafe.util.CorrelatedReaderTest subreader <../parser/test/compare-exprs-big.j
	#${JAVA} javafe.util.CorrelatedReaderTest reset <../parser/test/compare-exprs-big.j
	#
	# This test is disabled  because it is only useful with a human
	# observing the output:
	#${JAVA} javafe.util.CorrelatedReaderTest locs <CorrelatedReader.java
