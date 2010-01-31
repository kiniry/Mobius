package crazyBuggy;

import funnyBuggy.BigBuggyClass.Mood;

/**
 * Here:
 * - public, protected, private fields
 * - public, protected, private methods
 * @author evka
 *
 */
public class RedBuggyClass {

  private /*@ spec_public @*/ String name;
  private /*@ spec_protected @*/ String secondName;
  int number; 
  public Mood currentMood;
  
  public int getName() {return 0;}
  public String getSecondName() {return null;}
  public int getNumber() {return number;}
  
  private void talk(){}
  protected void colourMe(){}
  private void sleep(){}
  
  //@ invariant number != 0;
  
  
}
