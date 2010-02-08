abstract Citizenlib= {

  flags startcat=Phrase;

  cat
    Phrase; Interrogative ; Object; Digits;Adverb;
    
  fun
    
    Quest : Interrogative -> Object-> Phrase;
    AtMost :  Object -> Digits -> Phrase;
    IsIt : Adverb -> Phrase;
    What:Interrogative;
    Name,Sex,Age :Object;
    One,Two,Three: Digits;
    Single:Adverb;
}



