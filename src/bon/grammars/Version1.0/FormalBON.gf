
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
    	NounPhrase = {s : Str};
  
      lin
	
       --Overall
       	MakeTextPunct phrase punctuation = {s = phrase.s};
       	MakeText phrase = {s = phrase.s};
      
        --Queries
        QuestNoun  i nounphrase  = {s = i.s ++ nounphrase.s};
        IsItAdj adjetive = {s = "BOOLEAN" ++ ":" ++ adjetive.s};
       	DoesItVerb verb = {s = "BOOLEAN" ++ ":" ++ verb.s};
       	IsNounNoun quantifier noun1 noun2 = {s = "VALUE" ++ ":" ++ noun2.s};
	IsTheNounVerb quantifier noun verb = {s = "BOOLEAN" ++ ":" ++ verb.s} ;             
	--CommandVerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));

       	--Constraints
       	AtMostLeast  numeraladverb number noun = {s = noun.s ++ ".count" ++ numeraladverb.s  ++ number.s};   --REMOVE SPACE
       	
       	
       	--Noun Phrases
       	PronounNounPhrase  pronoun noun = {s = pronoun.s ++ noun.s};
       	
       	       
	--VerbPhrases
	       
	              
        --AdjetivePhrases
        AdjetivePhrase a = mkUtt(mkVP a);
       	
       	--Noun
       	Object n = mkUtt (mkNP(mkCN n));
        
        --Verb
        Action v = mkUtt(mkVP v);
        
        
        
        --Interogatives
        What = {s = "VALUE "} ;
        Who = {s = "VALUE "} ;
        
        --Pronouns
        Its = {s = ":"} ;
        
        --Digits
	One = {s = "1"};
	Two = {s = "2"};
	Three = {s = "3"};
	
	--Numeral Adverbs
	AtMost = {s = "<="};
        AtLeast = {s = ">="};
        --MoreThan = {s = ">"};
        --LessThan = {s = ">"};
        
        --Quantifiers
        The = {s = ""};
	A_Quant = {s = ""};
	That = {s = ""};
	This = {s = ""};
	No = {s = ""};
	
	--Puntuation
	FullStop = {s = "Constraint"} ;
	Exclamation = {s = "Command"}; 
       	QuestionMark = {s = "Query"};

        
               
    }