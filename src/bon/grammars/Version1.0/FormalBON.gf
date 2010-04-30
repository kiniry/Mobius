    --# -path=.:../alltenses

    
    concrete FormalBON of BONAbs = DictEng, NumeralEng ** open SyntaxEng,ParadigmsEng in {

      lincat
        Output = { s : Str};      
        Phrase= {s : Str};
        Sentence = {s : Str};
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
  
      lin
	
       --Overall
       	MakeTextPunct phrase punctuation = {s = phrase.s};
       	MakeText phrase = {s = phrase.s};
       	MakeTextSentence  sentence = {s = sentence.s};
      
        --Queries
        QuestNoun  i nounphrase  = {s = nounphrase.s ++ i.s };
        IsItAdj adjetive = {s = adjetive.s ++ ":" ++ "BOOLEAN"};
       	DoesItVerb verb = {s =  verb.s  ++ ":" ++ "BOOLEAN"};
       	IsItVerb verbphrase = {s = verbphrase.s  ++ ":" ++ "BOOLEAN"};
       	IsNounNoun quantifier noun1 noun2 = {s = noun2.s ++ ":" ++ "VALUE" ++ "(" ++ quantifier.s ++ noun1.s ++")"};
	IsTheNounVerb quantifier noun verb = {s =  verb.s ++ ":" ++ "BOOLEAN" ++ "(" ++ quantifier.s ++ noun.s ++")"};
	HowManyNoun idet noun = {s = noun.s ++ ":" ++ idet.s};
        WhichNoun iquant noun =   {s = iquant.s ++ ":" ++ noun.s};
        --CommandVerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));
       
        --Commands
        ShortCommand imp  = {s = imp.s};
        ActionCommand v = mkUtt (mkImp v); -- returns imp i.e go
        ActionNounCommand v2 n =mkUtt( mkImp v2 (mkNP (mkCN n)));-- returns imp i.e move  car
        ModifyActionCommand v adv = mkUtt (mkImp (mkVP (mkVP v) adv));-- returns imp i.e move right

       	--Constraints
       	AtMostLeast  numeraladverb number noun = {s = noun.s ++ ".count" ++ numeraladverb.s  ++ number.s};
       	--CanMust complementverb verb = mkS( mkCl(mkVP  complementverb (mkVP verb)));
        --CannotMustnot complementverb verb = mkS negativePol ( mkCl(mkVP  complementverb (mkVP verb)));
        NounHasNumberAtMost quantifier noun1 verb2 numeraladverb number noun2 = {s = noun2.s ++ ".count" ++ numeraladverb.s  ++ number.s ++"(" ++ quantifier.s ++verb2.s ++ noun1.s ++")"};
	ItHasNumberAtLeast  pronoun verb2 numeraladverb number noun =  {s = noun.s ++".count" ++ numeraladverb.s  ++ number.s ++ "(" ++ pronoun.s ++verb2.s  ++")"};
	NounHasNumber quantifier noun1 verb2  number noun2 = {s = noun2.s ++ ".count" ++ "=" ++ number.s ++"(" ++ quantifier.s ++noun1.s ++ verb2.s ++")"};--REMOVE SPACE
        ItHasNumber  pronoun verb2  number noun = {s = noun.s ++ ".count" ++ "="  ++ number.s ++"(" ++ pronoun.s ++ verb2.s ++ ")"};
       	
       	
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
        ModifyAction adv = mkUtt(mkVP adv);
        
        
        
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
        --MoreThan = {s = ">"};
        --LessThan = {s = ">"};
        
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

        
               
    }