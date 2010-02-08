abstract Citizenlib= {

  flags startcat=Phrase;

  cat
    Phrase; Interrogative ; Person ; Object;
    
  fun
    
    Is : Interrogative -> Person -> Object -> Phrase;
    What, Who: Interrogative;
    You:Person;
    Name,Sex,Age,MaritalStatus,Spouse,Children,Parent,Impediment:Object;
}



