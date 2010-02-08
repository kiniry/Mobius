    --# -path=.:../alltenses

    
    concrete CitizenlibEng of Citizenlib = DictEng ** open SyntaxEng,ParadigmsEng in{
  
      lincat
        Phrase = Phr;
        Interrogative=IP;
        
  
      lin
        Quest i n =mkPhr(mkQS (mkQCl i (mkNP it_Pron (mkCN n))));  
        What = whatSg_IP;
	
    } 