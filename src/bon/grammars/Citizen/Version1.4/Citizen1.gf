abstract Citizen1 = {

  flags startcat=Phrase;

  cat
    Phrase; Interrogative ; Owner ; Property;
    Requirement;Amount;Relations;
    
  fun
    
    Is : Interrogative -> Owner -> Property -> Phrase;
    Are : Interrogative -> Owner -> Property -> Phrase;
    DoHave : Interrogative -> Owner -> Property -> Phrase;
    What, Who , Do: Interrogative;
    Your, That,You:Owner;
    Name,Sex,Age,MaritalStatus,Spouse,Children,Parents,Impediment:Property;
    Citizen:Requirement ->  Property -> Phrase;
    Equals:Requirement -> Property -> Amount ->Phrase;
    Relation:Requirement -> Relations -> Property ->Phrase;
    Maximum:Requirement ->Amount -> Property -> Phrase;
    MoreThan: Amount -> Amount ;
    Marry: Requirement -> Requirement;
    Be: Requirement -> Requirement;
    Have: Requirement -> Requirement;
    Must,Cannot,NumberOf:Requirement;
    Two, One:Amount;
    Spouses,Childrens:Relations;
}