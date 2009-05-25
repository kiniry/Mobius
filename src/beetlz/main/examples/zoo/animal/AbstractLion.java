
package zoo.animal;

import java.util.List;  

//Use this class for JML assertions
public abstract class AbstractLion extends Animal implements Cloneable{
  
  public AbstractLion(List < String > [] name){}   
  
  public void feed(double amount) {    }
  
  
  public /*@ pure @*/ boolean isHappy() {return true;}
  
  private void wakeWakeUp() {}
    
  public class Mane{
    public Mane(){}
    
  }   
  
  
  
  private class Prey{}
}
