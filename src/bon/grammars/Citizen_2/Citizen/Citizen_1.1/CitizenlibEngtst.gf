    --# -path=.:../alltenses

    
    concrete CitizenlibEngtst of Citizenlibtst = open SyntaxEng,ParadigmsEng in{
  
      lincat
        Question = NP;
        Object= CN;
  
      lin
        Quest  o = mkNP it_Pron o;
	Name = mkCN name_N;
      oper
        name_N = mkN "name";
       
	}