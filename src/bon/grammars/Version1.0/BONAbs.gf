abstract BONAbs = DictEngAbs ** {

  flags startcat=Output;

  cat
    
    Output;
    Phrase; 
    Interrogative ;
    Noun;
    Adjetive;
    Verb;
    Pronoun;
    Number;
    NumeralAdverb;
    Verb2;
    Quantifier;
    Imperative;
    Adverb;
    Punctuation;
    
    
   
    
    
  fun
  
    MakeTextPunct : Phrase -> Punctuation -> Output;  
    MakeText : Phrase -> Output;
    QuestNoun :  Interrogative ->Pronoun ->Noun -> Phrase;
    DoesItVerb : Verb -> Phrase;
    IsItAdj : Adjetive -> Phrase;
    AtMostLeast : NumeralAdverb -> Number -> Noun -> Phrase;
    IsNounNoun: Quantifier -> Noun -> Noun -> Phrase;
    IsTheNounVerb: Quantifier -> Noun -> Verb -> Phrase;
    CommandVerbNoun: Verb2 -> Noun -> Phrase;
    ShortCommand:Imperative -> Phrase;
    
    
    Action : V -> Verb;
    Object : N -> Noun;
    ModifyAction : Adv -> Adverb;
    AdjetivePhrase: A -> Adjetive;
    TwoPlaceAction : V2 -> Verb2;
    ActionCommand : V -> Imperative;
    ActionNounCommand : Verb2 -> Quantifier -> Noun -> Imperative;
    ModifyActionCommand : Verb -> Adverb -> Imperative;
    
    
    

    What,Who:Interrogative;
    Its:Pronoun;
    One,Two,Three:Number;
    AtMost,AtLeast: NumeralAdverb;
    The,A_Quant,That,This,No: Quantifier;
    FullStop,Exclamation,QuestionMark: Punctuation;
    
        
    --QuestVerbNoun : V -> N -> Phrase;
    
    
   
  

}



