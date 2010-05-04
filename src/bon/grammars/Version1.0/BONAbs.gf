abstract BONAbs = DictEngAbs, Numeral ** {

  flags startcat=Output;

  cat
    
    Output;
    Phrase; 
    Sentence;
    SentenceList;
    Interrogative ;
    Noun;
    Adjetive;
    Verb;
    ComplementVerb;
    VerbPhrase;
    Pronoun;
    Number;
    NumeralAdverb;
    Verb2;
    IQuantifier;
    IDeterminer;
    Quantifier;
    Imperative;
    Adverb;
    Punctuation;
    NounPhrase;
    Conjunction;
    CAdverb ;
    
    
   
    
    
  fun
  
    --Overall  
    MakeText : Phrase -> Punctuation -> Output;  
    MakeTextSentence : Sentence -> Output;
    --MakeSentenceFromList : Conjunction -> SentenceList -> Sentence;
    MakeSentenceConj : Conjunction -> Sentence -> Sentence -> Sentence;
    --MakeSentenceList : Sentence -> Sentence -> SentenceList;
    --AddToSentenceList : Sentence -> SentenceList -> SentenceList;
    
    
    --Queries
    WhatIsTheNounsNoun : Noun -> Noun -> Phrase;
    WhatQuestValue: Phrase;
    WhatQuestNoun :  NounPhrase -> Phrase;
    WhoQuestNoun :  NounPhrase -> Phrase;
    DoesItVerb : Verb -> Phrase;
    DoesTheNounVerb : Noun -> Verb -> Phrase;
    IsItVerb : VerbPhrase -> Phrase;
    IsNounVerb : Noun -> VerbPhrase -> Phrase;
    IsItVerbAdv : VerbPhrase -> Adverb -> Phrase;
    IsNounVerbAdv : Noun -> VerbPhrase -> Adverb -> Phrase;
    IsItAdj : Adjetive -> Phrase;
    IsTheNounANoun:  Noun -> Noun -> Phrase;
    IsANounANoun:  Noun -> Noun -> Phrase;
    HowManyNoun :IDeterminer -> Noun -> Phrase;
    WhichNoun : IQuantifier -> Noun  -> Phrase;
    VerbNoun: Verb2 -> Noun -> Phrase;
    
    
    --Commands
    ShortCommand:Imperative -> Phrase;
    ActionCommand : V -> Imperative;
    ActionNounCommand : V2 ->  N -> Imperative;
    ModifyActionCommand : V -> Adv -> Imperative;
   
    
    
    
    --Constraints
    
    CanMust : ComplementVerb -> Verb -> Sentence;
    CannotMustnot : ComplementVerb -> Verb -> Sentence;
    AtMostLeast : NumeralAdverb -> Number -> Noun -> Sentence;
    ANounHasNumberAtMost: Noun ->  NumeralAdverb -> Number -> Noun -> Sentence;
    TheNounHasNumberAtMost: Noun ->  NumeralAdverb -> Number -> Noun -> Sentence;
    ItHasNumberAtLeast:   NumeralAdverb -> Number -> Noun -> Sentence;
    ItHasNumber:Number -> Noun -> Sentence;
    ANounHasNumber: Noun ->  Number -> Noun -> Sentence;
    TheNounHasNumber: Noun ->  Number -> Noun -> Sentence;
    TheNounExists:  Noun -> Sentence;
    ANounExists:  Noun -> Sentence;
    NoNounExists: Noun -> Sentence;
    TheNounIsNoun:Noun ->Noun ->Sentence;
    TheNounIsNotNoun:Noun ->Noun ->Sentence;
    ANounIsNoun:Noun ->Noun ->Sentence;
    ANounIsNotNoun:Noun ->Noun ->Sentence;
    
    
    --Noun Phrases
    PronounNounPhrase : Pronoun ->Noun -> NounPhrase;
    
    --Verb Phrases
    ProgressiveVerbPhrase : V -> VerbPhrase;
    
    Action : V -> Verb;
    Object : N -> Noun;
    ModifyAction : Adv -> Adverb;
    AdjetivePhrase: A -> Adjetive;
    TwoPlaceAction : V2 -> Verb2;
    Numbers : Digits -> Number;
    
    
    
    
    
    What,Who:Interrogative;
    Its:Pronoun;
    Which : IQuantifier;
    HowMany: IDeterminer;
    AtMost,AtLeast,MoreThan,LessThan: NumeralAdverb;
    The,QuantA,That,This,No: Quantifier;
    FullStop,Exclamation,QuestionMark: Punctuation;
    Can,Must: ComplementVerb;
    ConjunctionOr, ConjunctionAnd : Conjunction;
    --More,Less: CAdverb;
    
    
    
        

    
    
   
  

}



