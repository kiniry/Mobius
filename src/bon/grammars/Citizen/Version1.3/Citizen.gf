abstract Citizen = {

  flags startcat=Phrase ;

  cat
    Phrase ; Item ; Kind ; Quality ;
    Move ;      -- declarative, question, or imperative


  fun
    MAssert : Phrase -> Move ;  -- This pizza is warm.
    MDeny : Phrase -> Move ;    -- This pizza isn't warm.
    MAsk : Phrase -> Move ;     -- Is this pizza warm?
    Is : Item -> Quality -> Phrase ;
    This, That, These, Those : Kind -> Item ;
    QKind : Quality -> Kind -> Kind ;
    Wine, Cheese, Fish, Pizza : Kind ;
    Very : Quality -> Quality ;
    Fresh, Warm, Italian, Expensive, Delicious, Boring : Quality ;

}
