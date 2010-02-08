abstract Constraint = {

  flags startcat=Constraint ;

  cat
    Property;
    Requirement;Verb;Constraint;Amount;
    
  fun
    
    Citizen:Requirement -> Verb -> Property -> Constraint;
    Equals:Requirement -> Property -> Amount ->Constraint;
    Must,Cannot,NumberOf:Requirement;
    Name,Sex,Age,MaritalStatus,Spouse,Children,Parents,Impediment:Property;
    Marry,Be,Have:Verb;
    Two:Amount;
}