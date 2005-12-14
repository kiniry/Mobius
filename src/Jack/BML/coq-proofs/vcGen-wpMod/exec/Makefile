FILES=semantique.vo wp.vo wpMod.vo proof1.vo

all: clean noclean

noclean: $(FILES)

%.vo : %.v
	coqc $<

clean: 
	rm -f *.vo *~
