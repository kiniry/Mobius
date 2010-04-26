
    --# -path=.:../alltenses

    
    concrete FormalBON of BONAbs = DictEng ** open SyntaxEng,ParadigmsEng in {

      lincat
        Output = { s : Str};      
        Phrase= {s : Str};
        Noun = {s : Str};
        Interrogative= {s : Str};
        Adjetive = {s : Str};
        Verb = {s : Str};
        Verb2 = {s : Str};
        Pronoun = {s : Str};
        Number = {s : Str};
    	NumeralAdverb = {s : Str};
    	Quantifier = {s : Str};
	Imperative = {s : Str};
	Adverb = {s : Str};
    	Punctuation = {s : Str};
  
      lin
	
       MakeTextPunct phrase punctuation = {s = phrase.s ++ punctuation.s};
       MakeText phrase = {s = phrase.s};
      
        --Queries
        QuestNoun  i p noun  = {s = i.s ++ p.s ++ noun.s};
        IsItAdj adjetive = {s = "BOOLEAN" ++ ":" ++ adjetive.s};
       	DoesItVerb verb = {s = "BOOLEAN" ++ ":" ++ verb.s};
       	
       	IsNounNoun quantifier noun1 noun2 = {s = "VALUE" ++ ":" ++ noun2.s};
	
	IsTheNounVerb quantifier noun verb = {s = "BOOLEAN" ++ ":" ++ verb.s};
	       
	       
	--CommandVerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));
       
       	
       	
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
        The = {s = ""};
	A_Quant = {s = ""};
	That = {s = ""};
	This = {s = ""};
	No = {s = ""};
	FullStop = {s = "Constraint"} ;
	Exclamation = {s = "Command"}; 
       	QuestionMark = {s = "Query"};

        
               
    }