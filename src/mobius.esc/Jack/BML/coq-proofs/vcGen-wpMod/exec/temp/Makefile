FILES= wpAssumeAux.vo  semantiqueAux.vo wpModAux.vo transformationAux.vo 

all: clean noclean

noclean: $(FILES)

%.vo : 
	coqc semantiqueAux
	coqc wpModAux
	coqc wpAssumeAux
	coqc transformationAux

clean: 
	rm -f *.vo *~
