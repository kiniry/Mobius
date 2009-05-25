package zoo.animal;

import java.util.Set;

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
  //@ensures sleeping ==> pissed == true;
  public void feed(double amount) {    }
  
  //@requires sleeping == true;
  //@assignable sleeping;
  //@ensures sleeping == false;
  public void wakeUp() {}
  
  //@assignable \everything;
  public void makePicture() {}
  
  //@assignable stripes[2];
  public void paintOver() {}
  
  //@invariant weight > 0; 
}
