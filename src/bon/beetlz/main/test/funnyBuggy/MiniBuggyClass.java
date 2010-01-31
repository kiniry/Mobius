package funnyBuggy;

/**
 * Here:
 * - extends clause
 * - interfaces
 * - Java intern interface
 * - interface and extends related methods
 * @author evka
 *
 */
public final class MiniBuggyClass extends SmallBuggyClass implements ScalableBuggy, Comparable<SmallBuggyClass> {

  public static void main(final String[] some_args) { }
  
  
  @Override
  public /*@ pure @*/ int compareTo(SmallBuggyClass arg0) { return 0;}

  @Override
  public boolean makeBig(int value) { return false;}

  @Override
  public void makeSmall(int value) { }

  @Override
  public void hide(double howLong) { }

  @Override
  public void vanish() { }

}
