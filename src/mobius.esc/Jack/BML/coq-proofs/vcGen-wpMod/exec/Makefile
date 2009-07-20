FILES=semantique.vo wp.vo wpMod.vo semantiqueAux.v  wpModAux.vo 

all: clean noclean

noclean: $(FILES)

%.vo : %.v
	~jcharles/mariela/jack_coqc -compile semantique
	~jcharles/mariela/jack_coqc -compile wp
	~jcharles/mariela/jack_coqc -compile wpMod
	~jcharles/mariela/jack_coqc -compile semantiqueAux
	~jcharles/mariela/jack_coqc -compile wpModAux
clean: 
	rm -f *.vo *~
