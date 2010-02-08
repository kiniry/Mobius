    --# -path=.:../alltenses

    
    concrete CitizenlibEng of Citizenlib = open SyntaxEng,ParadigmsEng in{
  
      lincat
        Phrase = Phr;
        Interrogative=IP;
        Object= N;
  
      lin
        Quest i o =mkPhr(mkQS (mkQCl i (mkNP it_Pron (mkCN o))));
          
        What = whatSg_IP;
	Name = name_N;
	Sex = sex_N;
	Age = age_N;
	
      oper
	name_N = mkN "name";
	sex_N = mkN "sex";
	age_N = mkN "age";
	
    } 