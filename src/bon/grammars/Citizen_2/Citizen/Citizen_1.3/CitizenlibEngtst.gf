    --# -path=.:../alltenses

    
    concrete CitizenlibEngtst of Citizenlibtst =  open SyntaxEng,ParadigmsEng in{
  
      lincat
      	Phrase = QCl;
        Interrogative = IP;
        Object = NP;
             
      lin
        WhatIs i n = mkQCl i n;
        Name = mkNP ( mkN "name");
        What = whatSg_IP;
      
	}