abstract Citizen1 = {

  flags startcat=Question ;

  cat
    Question; Interrogative ; Owner ; Property;
    
  fun
    
    Is : Interrogative -> Owner -> Property -> Question;
    Are : Interrogative -> Owner -> Property -> Question;
    What, Who : Interrogative;
    Your, That:Owner;
    Name,Sex,Age,MaritalStatus,Spouse,Children,Parents:Property;
    
}