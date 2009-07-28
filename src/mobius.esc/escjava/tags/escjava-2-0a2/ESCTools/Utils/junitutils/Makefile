
.PHONY: clean
clean:
	@rm -f *.class classes.stamp

.PHONY: build
build: classes.stamp

classes.stamp: *.java
	${JAVAC} -classpath ${JUNIT_LIB} $?
	touch classes.stamp

.PHONY: test
test:
