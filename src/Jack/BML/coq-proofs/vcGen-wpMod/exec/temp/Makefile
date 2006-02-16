FILES=semantiqueAux1.vo wpModAux1.vo  wpAssume1.vo transformation1.vo  

all: clean noclean

noclean: $(FILES)

%.vo : %.v
	~jcharles/mariela/jack_coqc -compile semantiqueAux1
	~jcharles/mariela/jack_coqc -compile wpModAux1
	~jcharles/mariela/jack_coqc -compile wpAssume1
	~jcharles/mariela/jack_coqc -compile  transformation1

clean: 
	rm -f *.vo *~
