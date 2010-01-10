package crazy;

import funny.BigClass.Mood;

/**
 * Here:
 * - public, protected, private fields
 * - public, protected, private methods
 * @author evka
 *
 */
public class RedClass {

  private /*@ spec_public @*/ String name;
  private /*@ spec_protected @*/ String secondName;
  int number; 
  public Mood currentMood;
  
  public String getName() {return name;}
  public String getSecondName() {return null;}
  public int getNumber() {return number;}
  
  public void talk(){}
  protected void colourMe(){}
  private void sleep(){}
  
  
  
  
}
