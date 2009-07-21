package defaultpackage;


//Use this class for JML and assertion language
public class ZebraTestRefined {
 private /*@ spec_public @*/ int  weight;
 private /*@ spec_public @*/ boolean  hungry;
 private /*@ spec_public @*/ boolean  pissed;
 private /*@ spec_protected @*/ boolean  sleeping;
 private /*@ spec_public @*/ String[] stripes;
   
 public int getWeight() {return weight;}
 public boolean isHungry() {return hungry;}
 public boolean isPissed() {return pissed;}
 public boolean isSleeping() {return true;}
 

  public void feed(double amount) {    }  
  
  public void wakeUp() {}
  
  void makePicture() {}
  
  void paintOver() {}
  
}
