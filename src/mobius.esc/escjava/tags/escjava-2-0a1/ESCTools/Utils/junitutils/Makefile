
.PHONY: clean
clean:
	@rm -f *.class classes.stamp

.PHONY: build
build: classes.stamp

classes.stamp: *.java
	javac -classpath ${JUNIT_LIB} $?
	touch classes.stamp

.PHONY: test
test:
