    concrete HelloEng of Hello = {
  
      lincat Greeting, Recipient = {s : Str} ;
  
      lin 
        Hello recip = {s = "hello" ++ recip.s} ;
        World = {s = "world"} ;
        Mum = {s = "mum"} ;
        Friends = {s = "friends"} ;
        Aidan = {s = "aidan"} ;
        Emma = {s = "emma"} ; 
        MorganMay = {s = "morgan"} ;
    }
