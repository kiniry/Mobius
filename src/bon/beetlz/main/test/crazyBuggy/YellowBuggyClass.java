package crazyBuggy;



/**
 * Here:
 * - complex JML statements
 * @author evka
 *
 */
public class YellowBuggyClass implements Dummy {
  
 public YellowBuggyClass(String s) {}
  
  public /*@ pure @*/ boolean find(String s){return false;}
  
  public void missing() {}

}
