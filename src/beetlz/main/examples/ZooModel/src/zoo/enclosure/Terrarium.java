package zoo.enclosure;

import java.util.List;
import java.util.Set;


public class Terrarium extends Enclosure{//<T extends AbstractAnimal, S> {
  
  //@assignable \nothing;
  public Set<?> temperature(){return null;}
  
  public void regulateTemperature(Set<? super Integer> temps){}
  
  public /*@ pure @*/ Set<Set<String>> heatUp(){ return null;}
}
