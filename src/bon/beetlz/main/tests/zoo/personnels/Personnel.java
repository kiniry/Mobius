/**
 * 
 */
package zoo.personnels;

/**
 * An interface for personnel of the zoo.
 */
public interface Personnel {
  public String name = "Mickey Mouse";  
  //@ public model String area;   
  public /*@ pure @*/ int getID();  
  public void setVacation();
  
  
}
