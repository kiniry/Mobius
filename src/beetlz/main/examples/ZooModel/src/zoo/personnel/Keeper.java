/**
 * 
 */
package zoo.personnel;


import zoo.animal.Animal;

/**
 * @author evka
 *
 */
public strictfp class Keeper implements Personnel{
  //public List < AbstractAnimal > animalsToLookAfter;
  
  private /*@ spec_public @*/ String name; 
  public /*@ pure @*/ String getName() {    return "";}
  
  @Override  
  public void setVacation() {}
  
  @Override
  public /*@ pure @*/ int getID(){return 0;}
   
  public boolean feedAnimal(Animal an){return true;}
  
  //Member class
  public static class Mop{ }

  public final class Brush{}
  
  

  
  
 
}
