
.PHONY: clean
clean:
	@rm -f *.class classes.stamp

.PHONY: build
build: classes.stamp

classes.stamp:
	javac -classpath ${JUNITLIB} *.java
	touch classes.stamp

.PHONY: test
test:
