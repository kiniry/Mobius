abstract BONAbs = DictEngAbs, Numeral ** {

  flags startcat=Output;

  cat
    
    Output;
    Phrase; 
    Sentence;
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
    
    
   
    
    
  fun
  
    --Overall  
    MakeTextPunct : Phrase -> Punctuation -> Output;  
    MakeText : Phrase -> Output;
    MakeTextSentence : Sentence -> Output;
    
    
    --Queries
    QuestNoun :  Interrogative ->NounPhrase -> Phrase;
    DoesItVerb : Verb -> Phrase;
    IsItVerb : VerbPhrase -> Phrase;
    IsItAdj : Adjetive -> Phrase;
    IsNounNoun: Quantifier -> Noun -> Noun -> Phrase;
    IsTheNounVerb: Quantifier -> Noun -> Verb -> Phrase;
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
    NounHasNumberAtMost: Quantifier ->Noun -> Verb2 -> NumeralAdverb -> Number -> Noun -> Sentence;
    ItHasNumberAtLeast:  Pronoun -> Verb2 -> NumeralAdverb -> Number -> Noun -> Sentence;
    NounHasNumber: Quantifier ->Noun -> Verb2 -> Number -> Noun -> Sentence;
    ItHasNumber:  Pronoun -> Verb2 -> Number -> Noun -> Sentence;
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
    AtMost,AtLeast: NumeralAdverb;
    The,QuantA,That,This,No: Quantifier;
    FullStop,Exclamation,QuestionMark: Punctuation;
    Can,Must: ComplementVerb;
    
    
    
        

    
    
   
  

}



