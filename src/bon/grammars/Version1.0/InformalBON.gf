    --# -path=.:../alltenses

    
    concrete InformalBON of BONAbs = DictEng,NumeralEng ** open SyntaxEng,ParadigmsEng in{
  
      lincat
        Output = Text;       
        Phrase = Phr;
        Sentence = S;
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
    	Punctuation = Punct;
    	NounPhrase = NP;
        
      lin
       
       --Overall
       MakeTextPunct phrase punctuation = mkText phrase punctuation;
       MakeText phrase = mkText phrase;
       MakeTextSentence  sentence = mkText sentence;
       
       --Queries
       QuestNoun i nounphrase =mkPhr(mkQS (mkQCl i nounphrase));
       IsItAdj adjetive = mkPhr(mkQS (mkCl(mkVP adjetive)));
       DoesItVerb verb = mkPhr(mkQS  (mkCl (mkVP verb)));
       IsItVerb verbphrase = mkPhr(mkQS  (mkCl verbphrase));
       IsNounNoun quantifier noun1 noun2 = mkPhr(mkQS (mkCl (mkNP  (mkDet quantifier)  noun1) (mkNP (mkDet a_Quant) noun2)));
       IsTheNounVerb quantifier noun verb = mkPhr(mkQS  (mkQCl (mkCl (mkNP  (mkDet quantifier)  noun) verb )));
       HowManyNoun idet noun = mkPhr(mkQS  (mkQCl (mkIP idet noun)));
       WhichNoun iquant noun =   mkPhr(mkQS  (mkQCl (mkIP iquant noun )));
       CommandVerbNoun  verb2 noun  =mkPhr(mkQS(mkCl (passiveVP verb2 (mkNP noun))));
      
       --Commands
       ShortCommand imp  = mkPhr( imp);
       ActionCommand v = mkImp v; -- returns imp i.e go
       ActionNounCommand v2 n = mkImp v2 (mkNP (mkCN n));-- returns imp i.e move the car
       ModifyActionCommand v adv = mkImp (mkVP (mkVP v) adv);-- returns imp i.e move right
       
       --Constraint
       AtMostLeast  numeraladverb number noun = mkS( mkCl(mkNP  (mkCard numeraladverb (mkCard number)) noun));
       CanMust complementverb verb = mkS( mkCl(mkVP  complementverb (mkVP verb)));
       CannotMustnot complementverb verb = mkS negativePol ( mkCl(mkVP  complementverb (mkVP verb)));
       NounHasNumberAtMost quantifier noun1 verb2 numeraladverb number noun2 = mkS( mkCl(mkNP (mkDet quantifier) noun1) verb2 (mkNP  (mkCard numeraladverb (mkCard number)) noun2));
       ItHasNumberAtLeast  pronoun verb2 numeraladverb number noun = mkS( mkCl(mkNP pronoun) verb2 (mkNP  (mkCard numeraladverb (mkCard number)) noun));
       NounHasNumber quantifier noun1 verb2  number noun2 = mkS( mkCl(mkNP (mkDet quantifier) noun1) verb2 (mkNP  (mkCard number) noun2));
       
       
       
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
       Who = whoSg_IP;
       Which = which_IQuant;
       HowMany = how8many_IDet;
      
       --Pronoun
       Its = it_Pron;
       
       --Digits
       Numbers d = d;

       
       --Numeral Adverb
       AtMost = at_most_AdN;
       AtLeast = at_least_AdN;
       --more = mkAdN more_CAdv;
       --Less = mkAdN less_CAdv;
       
       --Quantifier
       The = the_Quant;
       A_Quant = a_Quant;
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
	      
	
    } 