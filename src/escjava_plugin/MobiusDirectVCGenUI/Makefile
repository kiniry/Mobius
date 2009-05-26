DVCGEN=../MobiusDirectVCGen

prepare:
	mkdir -p lib
	cp ${DVCGEN}/lib/*.jar ./lib
	cp ${DVCGEN}/dist/*.jar ./lib
	cp ${DVCGEN}/logic/*.jar ./lib

chain:
	cd ../bico; make
	cd ../MobiusDirectVCGen; make prepare jar
	make prepare
	
