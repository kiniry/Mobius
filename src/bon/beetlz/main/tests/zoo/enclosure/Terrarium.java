package zoo.enclosure;
  
import java.util.Set;

import zoo.animal.Animal;


public class Terrarium <T extends Animal, S> extends Enclosure{// {
  
  //@assignable \nothing;
  public Set<?> temperature(){return null;}
  
  public void regulateTemperature(Set<? super Integer> temps){}
  
  public /*@ pure @*/ Set<Set<String>> heatUp(){ return null;}
}
