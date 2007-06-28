import java.util.*;
public class Patient extends Person {
  //@ public invariant 0 <= age && age <= 150;

  protected /*@ spec_public rep @*/ List history;
  /*@ public initially history.size() == 0;
    @ public invariant (\forall int i; 0 <= i && i < history.size();
    @                           history.get(i) instanceof rep String);
    @ public constraint \old(history.size()) <= history.size();
    @ public constraint (\forall int i; 0 <= i && i < \old(history.size());
    @                           history.get(i).equals(\old(history.get(i))));
    @*/

  /*@ requires !obs.equals("");
    @ assignable history.theCollection;
    @ ensures history.size() == \old(history.size()+1)
    @      && history.get(\old(history.size()+1)).equals(obs);   @*/
  public void recordVisit(String obs) {
    history.add(new /*@ rep @*/ String(obs));
  }

  //@ requires g.equals("female") || g.equals("male");
  //@ assignable gender, history;
  //@ ensures gender.equals(g);
  public Patient(String g) { super(g); history = new /*@ rep @*/ ArrayList(); }
}
