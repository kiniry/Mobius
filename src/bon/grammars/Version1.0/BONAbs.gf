abstract BONAbs = DictEngAbs ** {

  flags startcat=Phrase;

  cat
    Phrase; 
    Interrogative ;
    Noun;
    Adjetive;
    Verb;
    Pronoun;
    Number;
    NumeralAdverb;
    
    
   
    
    
  fun
    
    QuestNoun :  Interrogative ->Pronoun ->Noun -> Phrase;
    DoesItVerb : Verb -> Phrase;
    IsItAdj : Adjetive -> Phrase;
    AtMostLeast : NumeralAdverb -> Number -> Noun -> Phrase;
    --CommandVerbNoun: Noun -> Verb -> Phrase;
    
    Action : V -> Verb;
    Object : N -> Noun;
    AdjetivePhrase: A -> Adjetive;
    

    What,Who:Interrogative;
    Its:Pronoun;
    One,Two,Three:Number;
    AtMost,AtLeast: NumeralAdverb;
    
        --AtMost :  N -> Digits -> Phrase;
    --QuestVerbNoun : V -> N -> Phrase;
    --AtMost :  N -> Digits -> Phrase;
    --IsItAdj : Adjetive -> Phrase;
    --DoesItVerb : V -> Phrase;
    
   
  

}



