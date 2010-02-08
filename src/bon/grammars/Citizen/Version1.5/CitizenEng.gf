    concrete CitizenEng of Citizen1 = {
  
      lincat
        Phrase,Interrogative ,Owner,Property,Requirement,Amount,Relations= {s : Str} ;
  
      lin
        Is interrogative owner property = {s = interrogative.s ++ "is" ++ owner.s ++ property.s} ;
        Are interrogative owner property = {s = interrogative.s ++ "are" ++ owner.s ++ property.s} ;
        DoHave interrogative owner property = {s = interrogative.s ++ owner.s ++ "have an" ++ property.s} ;
        Citizen requirement property= {s = requirement.s ++ property.s};
    	Equals requirement property amount = {s = requirement.s ++ property.s ++ "equals" ++ amount.s};
    	Relation requirement relations property = {s = requirement.s ++ relations.s ++ property.s};
    	Maximum requirement amount property= {s = requirement.s ++ amount.s ++ property.s};
    	MoreThan amount= {s = "more than" ++ amount.s} ;
    	Marry requirement = {s = requirement.s ++ "marry"} ;
	Be requirement = {s = requirement.s ++ "be"} ;
        Have requirement = {s = requirement.s ++ "have"} ;
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