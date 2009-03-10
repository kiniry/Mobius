COQC=coqc


all: main
Type= A_type.vo

type:  $(Type)
Signature= A_signature.vo

signature: type $(Signature)
Main= A.vo

main: signature $(Main)



# implicit rules
%.vo : %.v
	$(COQC) $<

