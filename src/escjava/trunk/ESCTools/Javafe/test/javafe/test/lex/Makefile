# Copyright 2000, 2001, Compaq Computer Corporation

JAVA ?= java

clean:
	rm -rf *.class test*.out

#
# Testing using TestLex:
#

TESTOR=javafe.test.lex.TestLex

test1.out test2.out: test1.in test2.in
	${JAVA} ${TESTOR} < test1.in > test1.out
	${JAVA} ${TESTOR} < test2.in > test2.out

runtest: test1.out test2.out
	diff test1.out test1.ans
	diff test2.out test2.ans
