    --# -path=.:../alltenses

    
    concrete FormalBON of BONAbs = DictEng, NumeralEng ** open SyntaxEng,ParadigmsEng in {

      lincat
        Output = { s : Str};      
        Phrase= {s : Str};
        Sentence = {s : Str};
        SentenceList = {s : Str};
        Noun = {s : Str};
        Interrogative= {s : Str};
        Adjetive = {s : Str};
        Verb = {s : Str};
        ComplementVerb = {s : Str};
        Verb2 = {s : Str};
        VerbPhrase = {s : Str};
        Pronoun = {s : Str};
        Number = {s : Str};
    	NumeralAdverb = {s : Str};
    	Quantifier = {s : Str};
    	IQuantifier = {s : Str};
    	IDeterminer = {s : Str};
	Imperative = {s : Str};
	Adverb = {s : Str};
    	Punctuation = {s : Str};
    	NounPhrase = {s : Str};
    	Conjunction = {s : Str};
  
      lin
	
       --Overall
       	MakeText phrase punctuation = {s = phrase.s};
       	MakeTextSentence  sentence = {s = sentence.s};
       	--MakeSentenceFromList conjunction sentencelist = {s = sentencelist.s ++ conjunction.s};
	MakeSentenceConj conjunction sentence1 sentence2 = {s = sentence1.s ++ conjunction.s ++ sentence2.s};
	--MakeSentenceList sentence1 sentence2 = {s = sentence1.s ++ "," ++ sentence2.s};
        --AddToSentenceList sentence sentencelist = {s = sentencelist.s ++ "," ++ sentence.s};
      
        --Queries
        WhatQuestValue = {s = "value : INTEGER" };
        WhatQuestNoun  nounphrase  = {s = nounphrase.s ++ "VALUE" };
        WhoQuestNoun  nounphrase  = {s = nounphrase.s ++ "SET[]" };
        IsItAdj adjetive = {s = adjetive.s ++ ":" ++ "BOOLEAN"};
       	DoesItVerb verb = {s =  verb.s  ++ ":" ++ "BOOLEAN"};
       	IsItVerb verbphrase = {s = verbphrase.s  ++ ":" ++ "BOOLEAN"};
       	IsNounVerb noun verbphrase = {s = verbphrase.s  ++ ":" ++ "BOOLEAN"};
       	IsItVerbAdv verbphrase adverb = {s = verbphrase.s  ++ "_" ++ adverb.s ++ ":" ++ "BOOLEAN"};
       	IsNounVerbAdv noun verbphrase adverb = {s = verbphrase.s  ++ "_" ++ adverb.s ++ ":" ++ "BOOLEAN"};
       	IsTheNounANoun  noun1 noun2 = {s = noun1.s ++ ":" ++ "SET[" ++ noun2.s ++ "]" };
       	IsANounANoun  noun1 noun2 = {s = noun1.s ++ ":" ++ "SET[" ++ noun2.s ++ "]" };
	DoesTheNounVerb noun verb = {s =  verb.s ++ ":" ++ "BOOLEAN" ++ "("  ++ noun.s ++")"};
	HowManyNoun idet noun = {s = noun.s ++ ":" ++ idet.s};
        WhichNoun iquant noun =   {s = iquant.s ++ ":" ++ noun.s};
        --VerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));
       
        --Commands
        ShortCommand imp  = {s = imp.s};
        ActionCommand v = mkUtt (mkImp v); -- returns imp i.e go
        ActionNounCommand v2 n =mkUtt( mkImp v2 (mkNP (mkCN n)));-- returns imp i.e move  car
        ModifyActionCommand v adv = mkUtt (mkImp (mkVP (mkVP v) adv));-- returns imp i.e move right

       	--Constraints
       	AtMostLeast  numeraladverb number noun = {s = noun.s ++ ".count" ++ numeraladverb.s  ++ number.s};
       	CanMust complementverb verb = {s = complementverb.s ++ verb.s};
        --CannotMustnot complementverb verb = mkS negativePol ( mkCl(mkVP  complementverb (mkVP verb)));
        ANounHasNumberAtMost noun1  numeraladverb number noun2 = {s = noun2.s ++ ".count" ++ numeraladverb.s  ++ number.s };
        TheNounHasNumberAtMost noun1  numeraladverb number noun2 = {s = noun2.s ++ ".count" ++ numeraladverb.s  ++ number.s };
        ANounHasNumber noun1  number noun2 = {s = noun2.s ++ ".count" ++ "=" ++ number.s };
        TheNounHasNumber noun1  number noun2 = {s = noun2.s ++ ".count" ++ "=" ++ number.s };
        ItHasNumber number noun = {s = noun.s ++".count" ++ "=" ++ number.s };
	ItHasNumberAtLeast  numeraladverb number noun =  {s = noun.s ++".count" ++ numeraladverb.s  ++ number.s };
       	TheNounExists noun  =  {s=  noun.s ++ "/= VOID" };
       	ANounExists noun  =  {s=  noun.s ++ "/= VOID" };
       	NoNounExists noun  =  {s=  noun.s ++ "= VOID" };
       	TheNounIsNoun noun1 noun2 = {s=  noun1.s ++ "=" ++ noun2.s };
	TheNounIsNotNoun noun1 noun2 = {s=  noun1.s ++ "/=" ++ noun2.s };
	ANounIsNoun noun1 noun2 = {s=  noun1.s ++ "=" ++ noun2.s };
        ANounIsNotNoun noun1 noun2 = {s=  noun1.s ++ "/=" ++ noun2.s };
       	
       	--Noun Phrases
       	PronounNounPhrase  pronoun noun = {s = noun.s ++ pronoun.s};
       	
       	       
	--VerbPhrases
	ProgressiveVerbPhrase v = mkUtt (progressiveVP (mkVP v));
	       
	              
        --AdjetivePhrases
        AdjetivePhrase a = mkUtt(mkVP a);
       	
       	--Noun
       	Object n = mkUtt (mkNP(mkCN n));
        
        --Verb
        Action v = mkUtt(mkVP v);
        TwoPlaceAction v2 = mkUtt(reflexiveVP v2);
        ModifyAction adv = mkUtt(mkVP adv) ;
        
        
        
        --Interogatives
        What = {s = "VALUE "} ;
        Who = {s = "VALUE "} ;
        Which = {s = "VALUE "};
        HowMany = {s = "INTEGER"} ;
        
        --Pronouns
        Its = {s = ":"} ;
        
        --Digits
        Numbers d = mkUtt (mkCard d) ;
	
	--Numeral Adverbs
	AtMost = {s = "<="};
        AtLeast = {s = ">="};
        MoreThan = {s = ">"};
        LessThan = {s = "<"};
        
        --Quantifiers
        The = {s = "the"};
	A_Quant = {s = "a"};
	That = {s = "that"};
	This = {s = "this"};
	No = {s = "no"};
	
	--Puntuation
	FullStop = {s = "Constraint"} ;
	Exclamation = {s = "Command"}; 
       	QuestionMark = {s = "Query"};
       	
       --Complement_Verb
        Can = {s = "can"} ;
        Must = {s = "must"} ;
        
        --Conjunctions
        ConjunctionOr = {s = "or"} ;
        ConjunctionAnd = {s = "and"} ;

        
               
    }