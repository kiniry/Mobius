public class TestComparable extends LocalTestCase {

  Comparable c,cc;
  Object o;

  public void test() {}

  public void NEtest1() {
    //@ assume c != null && cc != null;
    //@ assume Comparable.definedComparison(c.getClass(), cc.getClass());
    int i = c.compareTo(c);
    //@ assert i == 0;
    i = c.compareTo(cc);
    int j = cc.compareTo(c);
    //@ assert i == -j;

    //@ assume o != null;
    //@ assume o.getClass() == \type(Object);
    try {
      c.compareTo(o);
      //@ assert false;
    } catch (Exception e) {
      //@ assert e instanceof ClassCastException;
    }

    Object oo = null;
    try {
      c.compareTo(oo);
      //@ assert false;
    } catch (Exception e) {
      //@ assert e instanceof NullPointerException;
    }

//@ assert false; // TEST FOR CONSISTENCY
  }
}
