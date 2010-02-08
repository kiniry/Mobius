abstract Citizen1 = {

  flags startcat=Phrase;

  cat
  parameters : Sg|Pl
    Phrase; Interrogative ; Owner ; Property;
    Requirement;Verb;Amount;Relations;

	Class; Query; Command; Constraint;
	Index; Requirement; Parameters;
	// probably from built-in libraries
    	Property; Verb; Declaration; Relation; Amount; Phrase;
    	InterrogativePhrase; CommandPhrase; Possessive;
  fun:
    InterrogativePhrase: Query -> Phrase
    CommandPhrase: Command -> Phrase
    Query: Class -> Parameters
    Parameters: Possesive -> Property
    Your, That, You: Possessive;

    Two, One: Amount;

    Equals:Requirement -> Property -> Amount ->Phrase;
    Relation:Requirement -> Verb -> Relations -> Property ->Phrase;
    Maximum:Requirement ->Verb -> Amount -> Property -> Phrase;
    MoreThan: Amount -> Amount ;
    Must, Cannot,NumberOf: Requirement;
    
    // general BON stuff
    IsA: Class -> Class -> Relation
    HasA: Class -> Property -> Relation

    Query : Interrogative -> Class -> Property -> InterrogativePhrase;
    Who, What, Where, When, Why, How, Do: Interrogative;

    Name, Sex, Age, MaritalStatus, Spouse, Children, Parents, Impediment: Property;
    Citizen:Requirement -> Verb -> Property -> Phrase;
    Marry, Be, Have: Verb;
    Spouses, Childrens: Relations;

}