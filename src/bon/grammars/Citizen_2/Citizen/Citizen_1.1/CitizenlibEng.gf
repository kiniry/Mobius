    --# -path=.:../alltenses

    
    concrete CitizenlibEng of Citizenlib = open SyntaxEng,ParadigmsEng in{
  
      lincat
        Question = Text;
        Interrogative=IP;
        Object= CN;
  
      lin
        Quest i o =mkText mkText(mkQS (mkQCl i)) mkText( mkCl (mkNP it_Pron o));
          
        What = whatSg_IP;
	Name = mkCN name_N;
	Sex = mkCN sex_N;
	Age = mkCN age_N;
	
      oper
	name_N = mkN "name";
	sex_N = mkN "sex";
	age_N = mkN "age";
	
    } 