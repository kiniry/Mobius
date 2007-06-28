public abstract class TableFind {

  protected /*@ spec_public @*/ String[] keys;
  protected /*@ spec_public @*/ Object[] vals;

  //@ public invariant keys.length == vals.length;

  /*@   public normal_behavior
    @     requires (\exists int i; 
    @              0 <= i && i < vals.length; 
    @              keys[i].equals(k));
    @     ensures (\exists int i; 
    @              0 <= i && i < vals.length; 
    @              keys[i].equals(k)
    @              && \result == vals[i]);
    @ also
    @   public exceptional_behavior
    @     requires !(\exists int i; 
    @               0 <= i && i < vals.length; 
    @               keys[i].equals(k));
    @     signals_only NotFoundException;
    @*/
  public /*@ pure @*/ get(String k)
        throws NotFoundException;
}
