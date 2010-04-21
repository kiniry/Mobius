
    --# -path=.:../alltenses

    
    concrete FormalBON of BONAbs = DictEng ** open SyntaxEng,ParadigmsEng in {

      lincat
        Phrase= {s : Str};
        Noun = {s : Str};
        Interrogative= {s : Str};
        Adjetive = {s : Str};
        Verb = {s : Str};
        Pronoun = {s : Str};
        Number = {s : Str};
    	NumeralAdverb = {s : Str};
  
      lin
        --Queries
        QuestNoun  i p noun  = {s = i.s ++ p.s ++ noun.s};
        IsItAdj adjetive = {s = "BOOLEAN" ++ ":" ++ adjetive.s};
       	DoesItVerb verb = {s = "BOOLEAN" ++ ":" ++ verb.s};
       	
       	--Constraints
       	AtMostLeast  numeraladverb number noun = {s = noun.s ++ numeraladverb.s  ++ number.s};
       	
       	Object n = mkUtt (mkNP(mkCN n));
        Action v = mkUtt(mkVP v);
        AdjetivePhrase a = mkUtt(mkVP a);
        
        What = {s = "VALUE "} ;
        Who = {s = "VALUE "} ;
        Its = {s = ":"} ;
	One = {s = "1"};
	Two = {s = "2"};
	Three = {s = "3"};
	AtMost = {s = "<="};
        AtLeast = {s = ">="};
        
               
    }