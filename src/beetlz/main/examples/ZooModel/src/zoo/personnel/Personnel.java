/**
 * 
 */
package zoo.personnel;

/**
 * @author evka
 *
 */
public interface Personnel {
  public String name = "Mickey Mouse";  
  //public String area = "zoo";   
  public /*@ pure @*/ int getID();  
  public void setVacation();
}
