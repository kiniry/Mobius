    --# -path=.:../alltenses

    
    concrete CitizenlibEngtst of Citizenlibtst =  open SyntaxEng,ParadigmsEng in{
  
      lincat
      	Phrase = QS;
        Interrogative = IP;
        Object = NP;
             
      lin
        WhatIs i n = mkQS(mkQCl i n);
        Name = mkNP ( mkN "name");
        What = whatSg_IP;
      
	}