/* immutable */ 
interface Pair
{
  /*@ normal_behavior
    @   modifies \nothing;
    @   ensures \result.first() == null 
    @        && \result.second() == null;
    @*/
  /*@ non_null @*/ Pair nullPair();

  /*@ normal_behavior
    @   modifies this.objectState;
    @   ensures \result.first() == first;
    @   ensures \result.second() == second;
    @*/
  /*@ non_null @*/ Pair make(Object first, Object second);

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  /*@ pure @*/ Object first();

  /*@ normal_behavior
    @   modifies \nothing;
    @*/
  /*@ pure @*/ Object second();
  
  /*@ also 
    @ normal_behavior
    @   ensures \result == (this == other);
    @   ensures \result == (\typeof(other) == \type(Pair) && ((Pair)other).first() == first() && ((Pair)other).second() == second());
    @*/
  /*@ pure @*/ boolean equals(Object other);
}
