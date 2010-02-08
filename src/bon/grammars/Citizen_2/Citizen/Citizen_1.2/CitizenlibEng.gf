    --# -path=.:../alltenses

    
    concrete CitizenlibEng of Citizenlib =  open SyntaxEng,ParadigmsEng in{
  
      lincat
        Phrase = Phr;
        Object= N;
        Number = Numeral;
  
      lin
        AtMost o n = mkPhr (mkUtt(mkNP  (mkCard at_most_AdN (mkCard n)) o));
        One = n1_Numeral;

	
	
    } 