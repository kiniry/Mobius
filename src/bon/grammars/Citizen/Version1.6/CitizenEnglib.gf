    --# -path=.:../foods:minimal:present

    
    concrete CitizenlibEng of Citizenlib = open SyntaxEng,ParadigmsEng in{
  
      lincat
        Question = QCL;
        Interrogative=IP;
        Object= CN;
  
      lin
        Quest i p = mkQCL i ( mkCl (mkNP it_Pron o));
          
        
	Name = mkCN name_N;
	Sex = mkCN sex_N;
	Age = mkCN age_N;
	
      oper
	name_N = mk_N "name";
	sex_N = mk_N "sex";
	age_N = mk_N "age";
	
    } 