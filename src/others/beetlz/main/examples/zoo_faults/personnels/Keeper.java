/**
 * 
 */
package zoo_faults.personnels;


import java.util.List;
import java.util.Set;

import zoo.animal.Animal;
import zoo.animal.Snake;

/**
 * A type of personnel that looks after the animals.
 */
public strictfp class Keeper implements Personnel{
  //public enum Food {FISH, GRASS, BLOD, ANYTHING}
  
  public List < Animal > animals;
  public final Animal favouriteAnimal;
  public final Animal secondFavouriteAnimal;
  
  //@ensures ! favouriteAnimal.equals(secondFavouriteAnimal);
  //@ensures \forall int i; 0 <= i && i < 7; animals.get(i) != null;
  public Keeper() {
    favouriteAnimal = new Snake(); 
    secondFavouriteAnimal = new Snake(); 
  }
  
  private /*@ spec_public @*/ String name; 
  public /*@ pure non_null @*/ String getName() {    return "";}
  
  @Override  
  public void setVacation() {}
  
  //@ensures feedAnimal == true;
  public /*@ nullable pure @*/ String goOnVacation(/*@ non_null @*/ String where) {return null;}
  
  
  @Override
  public /*@ pure @*/ int getID(){return 0;}
   
  
  public /*@ pure @*/ boolean feedAnimal(/*@ nullable @*/ Animal an){return true;}
  
  /**
   * A Mop is an 'integral' part of each Keeper.
   */
  public static class Mop{ }

  public final class Brush{}
  
  


  
 
}
