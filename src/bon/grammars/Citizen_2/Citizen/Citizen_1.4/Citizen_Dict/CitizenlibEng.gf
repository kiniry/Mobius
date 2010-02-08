    --# -path=.:../alltenses

    
    concrete CitizenlibEng of Citizenlib = DictEng ** open SyntaxEng,ParadigmsEng in{
  
      lincat
        Phrase = Phr;
        Interrogative=IP;
        Object= N;
  
      lin
        Quest i o =mkPhr(mkQS (mkQCl i (mkNP it_Pron (mkCN o))));  
        What = whatSg_IP;
	
    } 