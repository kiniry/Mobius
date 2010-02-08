    concrete ConstraintEng of Constraint= {
  
      lincat
        Property,Requirement,Verb,Constraint,Amount= {s : Str} ;
  
      lin
        Citizen requirement verb property= {s = requirement.s ++ verb.s ++ property.s};
    	Equals requirement property amount = {s = requirement.s ++ property.s ++ "equals" ++ amount.s};
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
        Marry= {s = "marry"};
        Be = {s = "be"};
        Have = {s = "have"};
    	Two = {s = "two"};
    } 