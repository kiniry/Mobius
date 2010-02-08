    --# -path=.:../alltenses

    
    concrete CitizenlibBON of Citizenlib = {
  
      lincat
        Phrase,Interrogative,Object,Digits,Adverb = {s : Str} ;
  
      lin
        Quest i o ={s = o.s ++ i.s};
        AtMost o d = {s =  o.s ++".count <=" ++ d.s};
        IsIt a = {s =  a.s ++": BOOLEAN" };
        
        What = {s = ": VALUE"} ;
	Name = {s = "name"};
	Sex = {s ="sex"};
	Age = {s = "age"};
	One = {s= "1"};
	Two = {s= "2"};
	Three = {s = "3"};
	Single={s ="single"};
	
	
    }