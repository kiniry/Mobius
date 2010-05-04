    --# -path=.:../alltenses

    
    concrete InformalBON of BONAbs = DictEng,NumeralEng ** open SyntaxEng,ParadigmsEng in{
  
      lincat
        Output = Text;       
        Phrase = Phr;
        Sentence = S;
        SentenceList = ListS;
        Interrogative=IP;
        Noun = CN;
        Adjetive = AP;
        Verb = V;
        ComplementVerb = VV;
        Verb2 = V2;
        VerbPhrase = VP;
        Pronoun = Pron;
        Number = Digits;
    	NumeralAdverb = AdN;
    	IQuantifier = IQuant;
    	IDeterminer = IDet;
    	Quantifier = Quant;
    	Imperative = Imp;
    	Adverb = Adv;
    	CAdverb = CAdv;
    	Punctuation = Punct;
    	NounPhrase = NP;
    	Conjunction = Conj;
    	
        
      lin
       
       --Overall
       MakeText phrase punctuation = mkText phrase punctuation;
       MakeTextSentence  sentence = mkText sentence;
       --MakeSentenceFromList conjunction sentencelist = mkS conjunction sentencelist;
       MakeSentenceConj conjunction sentence1 sentence2 = mkS conjunction sentence1 sentence2;
       --MakeSentenceList sentence1 sentence2 = mkListS sentence1 sentence2;
       --AddToSentenceList sentence sentencelist = mkListS sentence sentencelist;
       
       --Queries
       WhatQuestNoun  nounphrase =mkPhr(mkQS (mkQCl whatSg_IP nounphrase));
       WhatQuestValue  =mkPhr(mkQS (mkQCl whatSg_IP (mkNP it_Pron (mkCN value_N))));
       WhoQuestNoun  nounphrase =mkPhr(mkQS (mkQCl whoPl_IP nounphrase));
       IsItAdj adjetive = mkPhr(mkQS (mkCl(mkVP adjetive)));
       DoesItVerb verb = mkPhr(mkQS  (mkCl (mkVP verb)));
       DoesTheNounVerb noun verb = mkPhr(mkQS  (mkCl (mkNP (mkDet the_Quant) noun) (mkVP verb)));
       IsItVerb verbphrase = mkPhr(mkQS  (mkCl verbphrase));
       IsNounVerb noun verbphrase = mkPhr(mkQS  (mkCl (mkNP  (mkDet the_Quant)  noun) verbphrase));
       IsItVerbAdv verbphrase adverb = mkPhr(mkQS  (mkCl (mkVP verbphrase adverb)));
       IsNounVerbAdv noun verbphrase adverb = mkPhr(mkQS  (mkCl (mkNP  (mkDet the_Quant)  noun) (mkVP verbphrase adverb)));
       IsTheNounANoun noun1 noun2 = mkPhr(mkQS (mkCl (mkNP  (mkDet the_Quant)  noun1) (mkNP (mkDet a_Quant) noun2)));
       IsANounANoun noun1 noun2 = mkPhr(mkQS (mkCl (mkNP  (mkDet a_Quant)  noun1) (mkNP (mkDet a_Quant) noun2)));
       HowManyNoun idet noun = mkPhr(mkQS  (mkQCl (mkIP idet noun)));
       WhichNoun iquant noun =   mkPhr(mkQS  (mkQCl (mkIP iquant noun )));
       VerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));
      
       --Commands
       ShortCommand imp  = mkPhr( imp);
       ActionCommand v = mkImp v; -- returns imp i.e go
       ActionNounCommand v2 n = mkImp v2 (mkNP (mkCN n));-- returns imp i.e move the car
       ModifyActionCommand v adv = mkImp (mkVP (mkVP v) adv);-- returns imp i.e move right
       
       --Constraint
       AtMostLeast  numeraladverb number noun = mkS( mkCl(mkNP  (mkCard numeraladverb (mkCard number)) noun));
       CanMust complementverb verb = mkS( mkCl(mkVP  complementverb (mkVP verb)));	
       CannotMustnot complementverb verb = mkS negativePol ( mkCl(mkVP  complementverb (mkVP verb)));
       ANounHasNumberAtMost  noun1 numeraladverb number noun2 = mkS( mkCl(mkNP (mkDet a_Quant) noun1) have_V2 (mkNP  (mkCard numeraladverb (mkCard number)) noun2));
       TheNounHasNumberAtMost  noun1 numeraladverb number noun2 = mkS( mkCl(mkNP (mkDet the_Quant) noun1) have_V2 (mkNP  (mkCard numeraladverb (mkCard number)) noun2));
       ItHasNumberAtLeast  numeraladverb number noun = mkS( mkCl(mkNP it_Pron) have_V2 (mkNP  (mkCard numeraladverb (mkCard number)) noun));
       ItHasNumber  number noun = mkS( mkCl(mkNP it_Pron) have_V2 (mkNP  (mkCard number) noun));
       ANounHasNumber  noun1 number noun2 = mkS( mkCl(mkNP (mkDet a_Quant) noun1) have_V2 (mkNP  (mkCard number) noun2));
       TheNounHasNumber  noun1 number noun2 = mkS( mkCl(mkNP (mkDet the_Quant) noun1) have_V2 (mkNP  (mkCard number) noun2));
       TheNounExists  noun  =  mkS ( mkCl(mkNP (mkDet the_Quant) noun) exist_V);
       ANounExists noun  =  mkS( mkCl(mkNP (mkDet a_Quant) noun) exist_V);
       NoNounExists  noun  =  mkS ( mkCl(mkNP (mkDet no_Quant) noun) exist_V);
       TheNounIsNoun noun1 noun2 = mkS ( mkCl(mkNP (mkDet the_Quant) noun1) (mkVP (mkNP (mkDet a_Quant) noun2)));
       TheNounIsNotNoun noun1 noun2 = mkS negativePol ( mkCl(mkNP (mkDet the_Quant) noun1) (mkVP (mkNP (mkDet a_Quant) noun2)));
       ANounIsNoun noun1 noun2 = mkS ( mkCl(mkNP (mkDet a_Quant) noun1) (mkVP (mkNP (mkDet a_Quant) noun2)));
       ANounIsNotNoun noun1 noun2 = mkS negativePol ( mkCl(mkNP (mkDet a_Quant) noun1) (mkVP (mkNP (mkDet a_Quant) noun2)));
       
       -- NounPhrases
       
       PronounNounPhrase  pronoun noun = mkNP pronoun noun;
       
       
       --VerbPhrases
       ProgressiveVerbPhrase v = progressiveVP (mkVP v); 
       
       --AdjetivePhrases
       AdjetivePhrase a = mkAP a ;
       
       --Noun
       Object n =   mkCN n;
       
       
       --Verb
       Action v = v;
       TwoPlaceAction v2 = v2;
       ModifyAction adv = adv;
              
       --Interrogative
       What = whatSg_IP;
       Who = whoPl_IP;
       Which = which_IQuant;
       HowMany = how8many_IDet;
      
       --Pronoun
       Its = it_Pron;
       
       --Digits
       Numbers d = d;

       
       --Numeral Adverb
       AtMost = at_most_AdN;
       AtLeast = at_least_AdN;
       MoreThan = mkAdN "more than";
       LessThan = mkAdN "less than";
       --More = more_CAdv;
       --Less = less_CAdv;
       
       --Quantifier
       The = the_Quant;
       QuantA = a_Quant;
       That = that_Quant;
       This = this_Quant;
       No = no_Quant;
       
       --Punctuation
       FullStop = fullStopPunct;
       Exclamation = exclMarkPunct; 
       QuestionMark = questMarkPunct;
       
       --Complement_Verb
       Can = can_VV;
       Must = must_VV;
       
       --Conjunctios
       ConjunctionOr = or_Conj;
       ConjunctionAnd = and_Conj;	      
	
    } 