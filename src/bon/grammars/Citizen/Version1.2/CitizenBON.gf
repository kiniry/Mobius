    concrete CitizenBON of Citizen1 = {
  
      lincat
        Question, Interrogative , Owner , Property= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = property.s ++ owner.s ++ interrogative.s } ;
        Are interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        Have interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        What = {s = "VALUE"} ;
        Who = {s = "CITIZEN"} ;
        Do = {s = "Boolean"} ;
        Your = {s = ":"} ;
        That = {s = ":"} ;
        You = {s = ":"} ;
        Name = {s = "name"} ;
        Age = {s = "age"} ;
        Sex = {s = "sex"} ;
        MaritalStatus = {s = "maritial_status"} ;
        Children = {s = "children"} ;
        Spouse = {s = "spouse"} ;
        Parents= {s = "parents"} ;
        Impediment = {s = "can_marry"};
    }