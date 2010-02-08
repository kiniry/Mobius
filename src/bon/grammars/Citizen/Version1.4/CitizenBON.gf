    concrete CitizenBON of Citizen1 = {
  
      lincat
        Phrase, Interrogative , Owner , Propertyu,Requirement,Amount,Relations= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = property.s ++ owner.s ++ interrogative.s } ;
        Are interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        DoHave interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        Citizen requirement  property= {s = requirement.s ++  property.s};
        Equals requirement property amount = {s = property.s ++ requirement.s ++  "=" ++ amount.s};
        Relation requirement  relations property = {s = requirement.s  ++ relations.s ++ property.s};
    	Maximum requirement  amount property= {s = requirement.s ++ amount.s ++ property.s};
        MoreThan amount= {s = ">" ++ amount.s} ;
        Marry requirement = {s = requirement.s ++ "marry"} ;
	Be requirement = {s = requirement.s ++ "be"} ;
	Have requirement = {s = requirement.s ++ "have"} ;
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
        NumberOf = {s = ".count"};
	Must= {s = "Must"};
	Cannot= {s = "Cannot"};
    	Two = {s = "2"};
    	One = {s = "1"};
    	Spouses = {s = "spouses"};
    	Childrens = {s = "childrens"};
    }