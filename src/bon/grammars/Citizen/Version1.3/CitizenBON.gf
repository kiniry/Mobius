    concrete CitizenBON of Citizen1 = {
  
      lincat
        Phrase, Interrogative , Owner , Property= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = property.s ++ owner.s ++ interrogative.s } ;
        Are interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        DoHave interrogative owner property = {s = property.s ++ owner.s++ interrogative.s } ;
        Citizen requirement verb property= {s = requirement.s ++ verb.s ++ property.s};
        Equals requirement property amount = {s = property.s ++ requirement.s ++  "=" ++ amount.s};
        Relation requirement verb relations property = {s = requirement.s ++ verb.s ++ relations.s ++ property.s};
    	Maximum requirement verb amount property= {s = requirement.s ++ verb.s ++ amount.s ++ property.s};
        MoreThan amount= {s = ">" ++ amount.s} ;
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
	Marry= {s = "marry"};
	Be = {s = "be"};
	Have = {s = "have"};
    	Two = {s = "2"};
    	One = {s = "1"};
    	Spouses = {s = "spouses"};
    	Childrens = {s = "childrens"};
    }