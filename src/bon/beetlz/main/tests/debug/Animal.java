package debug;

  
/**
 * An abstract Animal.
 * @author evka
 * @version 1
 */
public abstract class Animal {  
	  private /*@ spec_public @*/ boolean sleeping = false;
    private /*@ spec_public @*/ int weight;
    private /*@ spec_public @*/ int feedingFrequency;
    
    public boolean isSleeping() { return true;}
    
    public void scareAwake() {}
    
    public abstract void wakeUp();
    
    public int getWeight(){return weight;}      
    
    public int getFeedingFrequency(){return feedingFrequency;}
    
    //@ensures \result == 10 || \result ==20 || \result ==30;
    public /*@ pure @*/ int dummyDummy() {return 0;}
    
}
