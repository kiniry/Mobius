    concrete CitizenEng of Citizen1 = {
  
      lincat
        Question, Interrogative , Owner , Property= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = interrogative.s ++ "is" ++ owner.s ++ property.s} ;
        Are interrogative owner property = {s = interrogative.s ++ "are" ++ owner.s ++ property.s} ;
        What = {s = "What"} ;
        Who = {s = "Who"} ;
        Your = {s = "your"} ;
        That = {s = "that"} ;
        Name = {s = "name"} ;
        Age = {s = "age"} ;
        Sex = {s = "sex"} ;
        MaritalStatus = {s = "maritial status"} ;
        Children = {s = "children"} ;
        Spouse = {s = "spouse"} ;
        Parents= {s = "parents"} ;
    } 