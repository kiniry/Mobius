
.PHONY: clean
clean:
	@rm -f *.class classes.stamp

.PHONY: build
build: classes.stamp

classes.stamp: *.java
	javac -classpath ${JUNITLIB} $?
	touch classes.stamp

.PHONY: test
test:
