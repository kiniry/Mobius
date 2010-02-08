    concrete CitizenEng of Citizen1 = {
  
      lincat
        Question, Interrogative , Owner , Property= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = interrogative.s ++ "is" ++ owner.s ++ property.s} ;
        Are interrogative owner property = {s = interrogative.s ++ "are" ++ owner.s ++ property.s} ;
        Have interrogative owner property = {s = interrogative.s ++ owner.s ++ "have an" ++ property.s} ;
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
    } 