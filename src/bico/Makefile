Type= java/lang/java_lang_String_type.vo bicoMap_type.vo
Signature= java/lang/java_lang_String_signature.vo bicoMap_signature.vo
Main= java/lang/java_lang_String.vo bicoMap.vo
Extra= 
all:  $(Extra)
$(Extra): $(Main)
$(Main): $(Signature)
$(Signature): $(Type)

clean:
	rm -f java/lang/java_lang_String_type.vo bicoMap_type.vo java/lang/java_lang_String_signature.vo bicoMap_signature.vo java/lang/java_lang_String.vo bicoMap.vo

# implicit rules
%.vo : %.v
	coqc $<

