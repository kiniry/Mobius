/**
 * 
 */
package zoo_faults.personnels;

/**
 * @author evka
 *
 */
public enum Food {  
  FISH("fish"), 
  GRASS("grass"), 
  BLOOD("blood"), 
  ANYTHING("anything");

  private final String type;

  private Food(final String type) {
    this.type = type;
  }
  
  
  public /*@ pure @*/ String getName(){ return type;}
}
