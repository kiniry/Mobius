javafiles =	$(wildcard *.java)

javakeyfiles =	$(wildcard *Key.java)

classfiles =	$(foreach javafile,$(javafiles),\
		$(subst .java,.class,$(javafile)))

keyclasses =	$(foreach javakeyfile,$(javakeyfiles),\
		$(subst .java,,$(javakeyfile)))

%.class: %.java
	javac -g -source 1.4 $<

.PHONY:	all run clean

all:	$(classfiles)

run:
	for i in $(keyclasses); \
	do \
	  CLASSPATH=..; java -ea problems.$$i; \
	done

clean:
	rm -f *.class
