import java.util.*;
public class Patient extends Person {
  //@ public invariant 0 <= age && age <= 150;

  protected /*@ spec_public rep @*/ List log;
  //@ public initially log.size() == 0;
  /*@ public invariant (\forall int i;
    @      0 <= i && i < log.size();
    @      log.get(i) instanceof rep String); @*/
  /*@ public constraint
    @      \old(log.size()) <= log.size();
    @ public constraint (\forall int i; 
    @      0 <= i && i < \old(log.size());
    @      log.get(i).equals(\old(log.get(i))));
    @*/

  /*@ requires !obs.equals("");
    @ assignable log.theCollection;
    @ ensures log.size() == \old(log.size()+1)
    @      && log.get(\old(log.size()+1)).equals(obs); 
    @*/
  public void recordVisit(String obs) {
    log.add(new /*@ rep @*/ String(obs));
  }

  //@ requires g.equals("female") || g.equals("male");
  //@ assignable gender, log;
  //@ ensures gender.equals(g);
  public Patient(String g) { super(g); log = new /*@ rep @*/ ArrayList(); }
}
