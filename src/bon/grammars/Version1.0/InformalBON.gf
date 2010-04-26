    --# -path=.:../alltenses

    
    concrete InformalBON of BONAbs = DictEng ** open SyntaxEng,ParadigmsEng in{
  
      lincat
        Output = Text;       
        Phrase = Phr;
        Interrogative=IP;
        Noun = CN;
        Adjetive = AP;
        Verb = V;
        Verb2 = V2;
        Pronoun = Pron;
        Number = Digits;
    	NumeralAdverb = AdN;
    	Quantifier = Quant;
    	Imperative = Imp;
    	Adverb = Adv;
    	Punctuation = Punct;
        
        
  
      lin
       
       MakeTextPunct phrase punctuation = mkText phrase punctuation;
       MakeText phrase = mkText phrase;
       
       
       -- Queries
       
       QuestNoun i p noun =mkPhr(mkQS (mkQCl i (mkNP p noun)));
       IsItAdj adjetive = mkPhr(mkQS (mkCl(mkVP adjetive)));
       DoesItVerb verb = mkPhr(mkQS  (mkCl (mkVP verb)));
       IsNounNoun quantifier noun1 noun2 = mkPhr(mkQS (mkCl (mkNP  (mkDet quantifier)  noun1) (mkNP (mkDet a_Quant) noun2)));
       IsTheNounVerb quantifier noun verb = mkPhr(mkQS  (mkQCl (mkCl (mkNP  (mkDet quantifier)  noun) verb )));
       
       
       CommandVerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));
       
       --Commands
       ShortCommand imp  = mkPhr( imp);
       
       ActionCommand v = mkImp v; -- returns imp i.e go
       ActionNounCommand verb2 quantifier noun = mkImp verb2 (mkNP (mkDet quantifier) noun);-- returns imp i.e move the car
       ModifyActionCommand verb adverb = mkImp (mkVP (mkVP verb) adverb);-- returns imp i.e move right
       
       --Constraint
       AtMostLeast  numeraladverb number noun = mkPhr( mkUtt(mkNP  (mkCard numeraladverb (mkCard number)) noun));
       
       
       Object n =   mkCN n;
       Action v = v;
       ModifyAction adv = adv;
       AdjetivePhrase a = mkAP(a);
       TwoPlaceAction v2 = v2 ;

       
       What = whatSg_IP;
       Who = whoSg_IP;
       Its = it_Pron;
       One = n1_Digits;
       Two = n2_Digits;
       Three = n3_Digits;
       AtMost = at_most_AdN;
       AtLeast = at_least_AdN;
       The = the_Quant;
       A_Quant = a_Quant;
       That = that_Quant;
       This = this_Quant;
       No = no_Quant;
       FullStop = fullStopPunct;
       Exclamation = exclMarkPunct; 
       QuestionMark = questMarkPunct;
       ---Commands
	
	--CommandVerbNoun v n =mkPhr(mkCl (mkNP(mkCN n)) v));
	
       ---Constraints
	
	--
	      
	
    } 