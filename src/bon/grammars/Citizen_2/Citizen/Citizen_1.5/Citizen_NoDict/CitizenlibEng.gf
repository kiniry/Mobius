    --# -path=.:../alltenses

    
    concrete CitizenlibEng of Citizenlib = open SyntaxEng,ParadigmsEng in{
  
      lincat
        Phrase = Phr;
        Interrogative=IP;
        Object= N;
        Digits = Digits;
        Adverb=A;
  
      lin
        Quest i o =mkPhr(mkQS (mkQCl i (mkNP it_Pron (mkCN o))));
        AtMost o d =mkPhr( mkUtt(mkNP  (mkCard at_most_AdN (mkCard d)) o));
        IsIt a = mkPhr(mkQS (mkQCl (mkCl(mkVP a))));
        
          
        What = whatSg_IP;
	Name = name_N;
	Sex = sex_N;
	Age = age_N;
	One = n1_Digits;
	Two = n2_Digits;
	Three = n3_Digits;
	Single = single_A;
	
      oper
	name_N = mkN "name";
	sex_N = mkN "sex";
	age_N = mkN "age";
	single_A = compoundA (mkA "single");
	
    } 