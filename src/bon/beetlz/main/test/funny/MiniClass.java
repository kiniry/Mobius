package funny;

/**
 * Here:
 * - extends clause
 * - interfaces
 * - Java intern interface
 * - interface and extends related methods
 * @author evka
 *
 */
public final class MiniClass extends SmallClass implements Scalable, Comparable<SmallClass> {

  public static void main(final String[] some_args) { }
  
  
  @Override
  public /*@ pure @*/ int compareTo(SmallClass arg0) { return 0;}

  @Override
  public void makeBig(int value) { }

  @Override
  public void makeSmall(int value) { }

  @Override
  public void hide(double howLong) { }

  @Override
  public void vanish() { }

  public void hello(List<? extends String> list) {}
}
