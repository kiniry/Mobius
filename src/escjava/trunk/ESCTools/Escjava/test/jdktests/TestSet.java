import java.util.*;

public class TestSet extends LocalTestCase {
  static E e = new E();
  static F f = new F();

  //@ ensures \result != null && \fresh(\result);
  //@ ensures \result.isEmpty();
  //@ ensures \result.containsNull;
  //@ ensures \result.elementType == \type(E);
  public Set newSet() {
    Set s = new HashSet();
    //@ set s.containsNull = true;
    //@ set s.elementType = \type(E);
    return s;
  }

  public void testAdd() {
    Set s = newSet();
    assertTrue( !s.contains(null));
    assertTrue( !s.contains(e));
    assertTrue( !s.contains(f));
    
    s.add(null);
    s.add(e);
    assertTrue( s.contains(null));
    assertTrue( s.contains(e));
    assertTrue( !s.contains(f));
    E ee = new E();
    assertTrue( !s.contains(ee));
  }

}

class E {}


class F {}
