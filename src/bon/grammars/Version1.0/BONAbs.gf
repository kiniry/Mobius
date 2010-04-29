abstract BONAbs = DictEngAbs ** {

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
    Pronoun;
    Number;
    NumeralAdverb;
    Verb2;
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
    IsItAdj : Adjetive -> Phrase;
    IsNounNoun: Quantifier -> Noun -> Noun -> Phrase;
    IsTheNounVerb: Quantifier -> Noun -> Verb -> Phrase;
    
    
    --Commands
    CommandVerbNoun: Verb2 -> Noun -> Phrase;
    ShortCommand:Imperative -> Phrase;
    ActionCommand : V -> Imperative;
    ActionNounCommand : Verb2 -> Quantifier -> Noun -> Imperative;
    ModifyActionCommand : Verb -> Adverb -> Imperative;
    
    
    
    --Constraints
    
    CanMust : ComplementVerb -> Verb -> Sentence;
    CannotMustnot : ComplementVerb -> Verb -> Sentence;
    AtMostLeast : NumeralAdverb -> Number -> Noun -> Sentence;
    
    NounHasNumberAtMost: Quantifier ->Noun -> Verb2 -> NumeralAdverb -> Number -> Noun -> Sentence;
    ItHasNumberAtLeast:  Pronoun -> Verb2 -> NumeralAdverb -> Number -> Noun -> Sentence;
    NounHasNumber: Quantifier ->Noun -> Verb2 -> Number -> Noun -> Sentence;
    ItHasNumber:  Pronoun -> Verb2 -> Number -> Noun -> Sentence;
    
    
    --Phrases
    PronounNounPhrase : Pronoun ->Noun -> NounPhrase;
    
    
    
    
    Action : V -> Verb;
    Object : N -> Noun;
    ModifyAction : Adv -> Adverb;
    AdjetivePhrase: A -> Adjetive;
    TwoPlaceAction : V2 -> Verb2;
    
    
    
    

    What,Who:Interrogative;
    Its:Pronoun;
    One,Two,Three:Number;
    AtMost,AtLeast: NumeralAdverb;
    The,A_Quant,That,This,No: Quantifier;
    FullStop,Exclamation,QuestionMark: Punctuation;
    Can,Must: ComplementVerb;
    
    
    
        

    
    
   
  

}



