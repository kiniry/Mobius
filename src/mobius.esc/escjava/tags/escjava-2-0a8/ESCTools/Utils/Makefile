
export TOP = ..
include ${TOP}/Makefile.defs

.PHONY: clean test build esctest
clean test build esctest:
	@${MAKE} -C junitutils $@

build: checkjunitjar

.PHONY: checkjunitjar
checkjunitjar:
	@if [ ! -e ${JUNIT_LIB} ]; then \
		echo Error: ${JUNIT_LIB} should be a version of junit.jar, but it does not exist ;\
		exit 1; \
	fi

.PHONY: docs
docs:
	@true

