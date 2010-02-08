abstract Citizen2 = {

  flags startcat=Phrase;

  cat
    Phrase; Interrogative ; Owner ; Property;
    Requirement;Verb;Amount;Relations;
    
  fun
    
    Is : Interrogative -> Owner -> Property -> Phrase;
    Are : Interrogative -> Owner -> Property -> Phrase;
    DoHave : Interrogative -> Owner -> Property -> Phrase;
    What, Who , Do: Interrogative;
    Your, That,You:Owner;
    Name,Sex,Age,MaritalStatus,Spouse,Children,Parents,Impediment:Property;
    Citizen:Requirement -> Verb -> Property -> Phrase;
    Equals:Requirement -> Property -> Amount ->Phrase;
    Relation:Requirement -> Verb -> Relations -> Property ->Phrase;
    Maximum:Requirement ->Verb -> Amount -> Property -> Phrase;
    MoreThan: Amount -> Amount ;
    Must,Cannot,NumberOf:Requirement;
    Marry,Be,Have:Verb;
    Two, One:Amount;
    Spouses,Childrens:Relations;
}