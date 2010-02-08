    --# -path=.:../alltenses

    
    concrete CitizenlibBON of Citizenlib = {
  
      lincat
        Phrase,Interrogative,Object = {s : Str} ;
  
      lin
        Quest i o ={s = i.s ++ o.s};
          
        What = {s = "VALUE :"} ;

	
	
    }