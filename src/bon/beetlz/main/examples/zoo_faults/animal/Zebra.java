package zoo_faults.animal;
  

//Use this class for JML and assertion language
public class Zebra {
 private /*@ spec_public @*/ int  weight;
 private /*@ spec_public @*/ boolean  hungry;
 private /*@ spec_public @*/ boolean  pissed;
 private /*@ spec_protected @*/ boolean  sleeping;
 private /*@ spec_public @*/ String[] stripes;
   
 public int getWeight() {return weight;}
 public boolean isHungry() {return hungry;}
 public boolean isPissed() {return pissed;}
 public boolean isSleeping() {return true;}
 
 
  
  //@assignable hungry, sleeping;
  //@ensures isPissed == true <== sleeping;
  //@ensures sleeping <=!=> !hungry;
 //@ensures (* don't feed if fat *);
  public void feed(double amount) {    }  
  
  //@requires isSleeping == true;
  //@assignable sleeping;
  //@ensures sleeping == false;
  public void wakeUp() {}
  
  //@assignable \everything;
  //@requires stripes[2] == "black stripe";
  void makePicture() {}
  
  //@assignable stripes[2];
  //@requires !pissed;
  //@requires sleeping && !hungry;
  //@ensures pissed || hungry;
  void paintOver() {}
  
  //@invariant weight > 0; 
}
