package funnyBuggy;

import java.util.Vector;

/**
 * Here:
 * - enum
 * - aggregation relation
 * - constructors
 * - class generics
 * @author evka
 *
 */
public class BigBuggyClass {
  
  public enum Mood { HAPPY, SAD, DUNNO }
 
  
  public BigBuggyClass(String n){}
  public BigBuggyClass(Mood m, String n) {}
  
  
  public class Uno<T, R>{}
  
  private class Due<S, T>{}
  
  public class Tre<T extends Vector<String>>{}
  
}
