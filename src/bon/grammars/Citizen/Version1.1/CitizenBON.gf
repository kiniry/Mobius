    concrete CitizenBON of Citizen1 = {
  
      lincat
        Question, Interrogative , Owner , Property= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = property.s ++ owner.s ++ interrogative.s } ;
        Are interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        What = {s = "VALUE"} ;
        Who = {s = "CITIZEN"} ;
        Your = {s = ":"} ;
        That = {s = ":"} ;
        Name = {s = "name"} ;
        Age = {s = "age"} ;
        Sex = {s = "sex"} ;
        MaritalStatus = {s = "maritial_status"} ;
        Children = {s = "children"} ;
        Spouse = {s = "spouse"} ;
        Parents= {s = "parents"} ;
    }