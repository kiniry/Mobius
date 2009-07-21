package zoo_faults.animal;
import zoo.enclosure.*;
  
/**
 * An abstract Animal.
 * @author evka
 * @version 1
 */
@Info (name = "Mickey Mouse", birthDate = "3/17/2009")
public abstract class Animal {  
    private /*@ spec_public @*/ boolean sleeping = false;
    private /*@ spec_public @*/ int weight;
    private /*@ spec_public @*/ int feedingFrequency;
    
    public zoo.enclosure.Enclosure place = new Enclosure();
    
    @SuppressWarnings("unchecked")
    public boolean isSleeping() { return true;}
    
    @Deprecated
    public void scareAwake() {}
    
    public abstract void wakeUp();
    
    public int getWeight(){return weight;}      
    
    public int getFeedingFrequency(){return feedingFrequency;}
    
    
}
