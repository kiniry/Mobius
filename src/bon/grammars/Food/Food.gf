    abstract Food = {
  
      flags startcat = Phrase ;
  
      cat
        Phrase ; Item ; Kind ; Quality ;
  
      fun
        Is : Item -> Quality -> Phrase ;
        This, That : Kind -> Item ;
        QKind : Quality -> Kind -> Kind ;
        Wine, Cheese, Fish,Pasta, Pizza,Beer : Kind ;
        Very : Quality -> Quality ;
        Fresh, Warm, Italian, Expensive, Delicious, Boring, Cold, Cheap : Quality ;
    }
