    --# -path=.:../foods:minimal:present

    
    concrete CitizenlibEng of Citizenlib = open SyntaxEng,ParadigmsEng in{
  
      lincat
        Question = QCL;
        Phrase = CL;
        Interrogative=IP;
        Person = NP;
        Object= CN;
  
      lin
        Quest i p = mkQCL i p ;
      
        
        What = {s = "What"} ;
        Who = {s = "Who"} ;
        Do = {s = "Do"} ;
        Your = {s = "your"} ;
        That = {s = "that"} ;
        You = {s = "you"} ;
        Name = {s = "name"} ;
        Age = {s = "age"} ;
        Sex = {s = "sex"} ;
        MaritalStatus = {s = "maritial status"} ;
        Children = {s = "children"} ;
        Spouse = {s = "spouse"} ;
        Parents= {s = "parents"} ;
        Impediment = {s = "impediment to marriage"};
        NumberOf = {s = "Number of"};
        Must= {s = "Must"};
        Cannot= {s = "Cannot"};
    	One = {s = "one"};
    	Two = {s = "two"};
    	Spouses = {s = "spouse's"};
    	Childrens = {s = "children's"};
    } 