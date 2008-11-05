
  private boolean eltsInv(CPair cpair) {
    return (cpair == null ||
            (\typeof(cpair.first) == \type(Pair) &&
             (cpair.second == null) || ((cpair.second instanceof CPair) &&
                                        elts_invariant((CPair)(cpair.second)))));
  }



    // look for pre-existing chain of elements (o, elts)
    for (Pair p = lists; p != null; p = (Pair)(p.second)) {
      List aList = (List)(p.first);
      Pair q = aList.elts;
      if (q.first == o && q.second == elts)
        return q;
    }
    Pair result = Pair.make(o, elts);
    lists = Pair.make(result, lists);
    return result;


  /*@
    private normal_behavior
      ensures \result == (p == null ||
    (p.first instanceof Pair &&
    (p.second == null) || ((p.second instanceof Pair) &&
                                                chain_invariant((Pair)(p.second)))));
  */
  private /*@ pure @*/ static boolean isChain() {
    return (p == null ||
            (p.first instanceof Pair &&
             (p.second == null) || ((p.second instanceof Pair) &&
                                    chain_invariant((Pair)(p.second)))));
  }
    

  // -----------------------------------------------------------------
  // Helpers

  /**
   * Look for the node current starting from start and stopping at
   * stop.  If we find it, return true, otherwise, return false.
   */
  private static /*@ pure @*/ boolean inChain(/*@ non_null @*/ Pair start,
                                              /*@ non_null @*/ Pair stop, 
                                              /*@ non_null @*/ Pair current) {
    for (Pair p = start;
         p != null && p != stop;
         p = (Pair)p.second) {
      if (p == current)
        return true;
    }
    return false;
  }

  /**
   * @return true if the chain starting with p is cyclic.
   */
  private static /*@ pure @*/ boolean cyclic(Pair p) {
    if (p == null)
      return false;
    Pair start = p;
    Pair stop = p;
    // invariant: there are no duplicates in between start and stop.
    for (Pair current = (Pair)start.second(); 
         current != null; 
         stop = current, current = (Pair)current.second()) {
      if (inChain(start, stop, current))
        return true;
    }
    return false;
  }
}

                                                
  /**
   * A chain is either null or an acyclic sequence of Cons cells
   * terminated by null.
   */
  /*@ private normal_behavior
    @   requires !cyclic(c);
    @   ensures \result == 
    @     (c.second == null || 
    @      (c.second instanceof Cons && isChain((Cons)c.second)));
    @*/
  private static /*@ pure @*/ boolean isChain(Cons c) {
    return c.second == null || 
      (c.second instanceof Cons && isChain((Cons)c.second));
  }

  /**
   * Look for the node current starting from start and stopping at
   * stop.  If we find it, return true, otherwise, return false.
   */
  private static /*@ pure @*/ boolean inChain(/*@ non_null @*/ Cons start,
                                              /*@ non_null @*/ Cons stop, 
                                              /*@ non_null @*/ Cons current) {
    for (Cons p = start;
         p instanceof Cons && p != stop;
         p = (Cons)p.second) {
      if (p == current)
        return true;
      if (!(p.second instanceof Cons))
        return false;
    }
    return false;
  }

  /**
   * @return true iff p is a chain and it is cyclic.
   */
  public static /*@ pure @*/ boolean acyclicChain(Cons p) {
    if (p == null)
      return true;
    if (!(p.second instanceof Cons))
      return false;
    Cons start = p;
    Cons stop = p;
    // invariant: there are no duplicates in between start and stop.
    for (Cons current = (Cons)start.second(); 
         current != null; 
         stop = current, current = (Cons)current.second()) {
      if (inChain(start, stop, current))
        return false;
      if (!(current.second instanceof Cons))
        return false;
    }
    return false;
  }


  /*@ public normal_behavior
    @   requires isChain(chain);
    @   ensures  \result == (chain == null
    @			? 0
    @			: 1 + lengthHelper((Cons)chain.second()));
    @
    @ pure private static \bigint lengthHelper(Cons c) {
    @   return chain == null
    @			? 0
    @			: 1 + lengthHelper((Cons)chain.second());
    @ }
    @*/

  /*@ public normal_behavior
    @   requires isChain(chain);
    @   ensures  \result == lengthHelper(c);
    @
    @ pure private static \bigint length(Cons c) {
    @   return lengthHelper(c);
    @ }
    @*/

  /*@ public model \bigint length;
    @              in objectState;
    @*/
  //@ private represents length <- length(elts);
  //@ public invariant 0 <= length;

  //@ private invariant_redundantly elts == null <==> 0 == length;
  //@ public  invariant_redundantly isEmpty() <==> 0 == length;


  /*@ private normal_behavior
    @   ensures \result <==>
    @       (p != null && (p.first() == k || inChainHelper((Cons)(p.second()), k)));
    @   ensures \result <==> getCached((Cons)(p.second()), k.elts) != null;
    @*/
  private static /*@ pure @*/ boolean inChainHelper(/* null */ Cons p,
                                                    /*@ non_null */ Sequence k) {
    return p != null && (p.first() == k || inChainHelper((Cons)(p.second()), k));
  }

  /*@ private normal_behavior
    @  ensures \result <==> inChainHelper(chain, k);
    @*/
  private static /*@ pure @*/ boolean inChain(/*@ non_null @*/ Sequence k) {
    for (Cons p = chain; p != null; p = (Cons)(p.second())) {
      if (p.first() == k)
        return true;
    }
    return false;
  }
