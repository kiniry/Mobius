
package zoo.animal;  


public class Snake extends Animal implements DangerousAnimal{
  public void feed(){}
  public void feed(int amount){}
  public void feed(String what){}
  public void feed(String what, String amount) {}
  public void feed(int amount, String what) {}
  
  protected volatile String patternOne;    
  protected transient String patternTwo;
  public static void countStripes(){}
  public final native void getPattern();
  public strictfp void dummy(){}    
  
  @Override
  public void wakeUp() {}
  
  
}
