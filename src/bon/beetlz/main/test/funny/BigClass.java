package funny;

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
public class BigClass {
  
  public enum Mood { HAPPY, SAD, DUNNO }
 
  
  public BigClass(String n){}
  public BigClass(Mood m, String n) {}
  
  
  public class Uno<T>{}
  
  public class Due<S, T>{}
  
  public class Tre<T extends Vector<String>>{}
  
}
