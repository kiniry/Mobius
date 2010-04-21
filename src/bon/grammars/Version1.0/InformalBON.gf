    --# -path=.:../alltenses

    
    concrete InformalBON of BONAbs = DictEng ** open SyntaxEng,ParadigmsEng in{
  
      lincat
        Phrase = Phr;
        Interrogative=IP;
        Noun = CN;
        Adjetive = AP;
        Verb = VP;
        Pronoun = Pron;
        Number = Digits;
    	NumeralAdverb = AdN;
        

        
        
  
      lin
        -- Queries
       QuestNoun i p noun =mkPhr(mkQS (mkQCl i (mkNP p noun)));
       IsItAdj adjetive = mkPhr(mkQS (mkCl(mkVP adjetive)));
       DoesItVerb verb = mkPhr(mkQS  (mkCl verb));
       
       --Commands
       --CommandVerbNoun noun verb  =mkPhr(mkCl (mkNP noun) verb);
       
       --Constraint
       AtMostLeast  numeraladverb number noun = mkPhr( mkUtt(mkNP  (mkCard numeraladverb (mkCard number)) noun));
       
       
       Object n =   mkCN n;
       Action v = mkVP v;
       AdjetivePhrase a = mkAP(a);
       
       What = whatSg_IP;
       Who = whoSg_IP;
       Its = it_Pron;
       One = n1_Digits;
       Two = n2_Digits;
       Three = n3_Digits;
       AtMost = at_most_AdN;
       AtLeast = at_least_AdN;
       
       ---Commands
	
	--CommandVerbNoun v n =mkPhr(mkCl (mkNP(mkCN n)) v));
	
       ---Constraints
	
	--
	      
	
    } 