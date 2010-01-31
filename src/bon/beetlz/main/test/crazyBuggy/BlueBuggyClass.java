package crazyBuggy;

import java.util.List;
import java.util.PriorityQueue;
import java.util.Vector;

/**
 * Here:
 * - return types
 * - loads parameters
 * - overloaded method
 * @author evka
 *
 */
public class BlueBuggyClass {
  
  
  public void funny(int i){}
  public void funny(int i, String s){}
  public void funny(int i, int j, String s){}
  public void funny(int i, String s, String ss, long l){}
  
  
  public /*@ pure @*/ Vector<String> copy(PriorityQueue<Integer> p, int i, double d, float f){return null;}
  public /*@ pure @*/ Vector<List<String>> copyCopy(PriorityQueue<Integer> p, 
      PriorityQueue<String> pp, double d, float f){return null;}
  
  
}
