public final class List
{
  /*@ public static invariant
    @   (\forall List p, q;; p == q <==> 
    @           p.isEmpty() && q.isEmpty() ||
    @		(!p.isEmpty() && !q.isEmpty() && 
    @            p.head() == q.head() && 
    @		 p.tail() == q.tail())
    @	);
    @*/

  private static /* null */ Pair lists = null;

  /*@ spec_public @*/ private /* null */ Pair elts;

  private List(Pair elts) {
    this.elts = elts;
  }

  /*@ public normal_behavior
    @   modifies \nothing;
    @   ensures \result.isEmpty();
    @*/
  public static /*@ pure non_null @*/ List empty() {
    // look for the empty list and if it exists return it
    return lookupAndMake(null);
  }

  /*@ public normal_behavior
    @   ensures \result <==> elts == null;
    @*/
  public /*@ pure @*/ boolean isEmpty() {
    return (elts == null);
  }

  /*@ public normal_behavior
    @   ensures !\result.isEmpty();
    @   ensures \result.head() == o;
    @   ensures \result.tail() == this;
    @*/
  public /*@ pure non_null @*/ List append(Object o) {
    return lookupAndMake(Pair.make(o, elts));
  }

  /*@ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures \result == elts.first();
    @*/
  public /*@ pure @*/ Object head() {
    return elts.first();
  }

  /*@ public normal_behavior
    @  requires !isEmpty();
    @  modifies \nothing;
    @  ensures \result.elts == elts.second();
    @*/
  public /*@ pure @*/ List tail() {
    Pair someElts = (Pair)(elts.second());
    List result = lookupAndMake(someElts);
    return result;
  }

  private static /*@ non_null @*/ List lookupAndMake(Pair elts) {
    List result = lookup(elts);
    if (result == null) {
      result = new List(elts);
      lists = Pair.make(result, lists);
    }
    return(result);
  }

  private static /*null*/ List lookup(/*null*/ Pair elts) {
    // look for pre-existing chain of elements elts
    for (Pair p = lists; p != null; p = (Pair)(p.second())) {
      List aList = (List)(p.first());
      Pair q = aList.elts;
      if (elts == q)
        return aList;
    }
    return null;
  }
}
