package mobius.cct.tests.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;

import mobius.cct.util.Function;
import mobius.cct.util.MappedIterator;

import org.junit.Test;

/**
 * Tests for class MappedIterator.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MappedIteratorTest {
  /**
   * Simple test.
   */
  @Test
  public void testSimple() {
    ArrayList<Integer> l = new ArrayList<Integer>();
    l.add(84);
    l.add(8);
    l.add(26);
    Function<Integer, Integer> f = new Function<Integer, Integer>() {

      public Integer call(Integer args) {
        return args + 42;
      }
      
    };
    MappedIterator<Integer, Integer> i = 
      new MappedIterator<Integer, Integer>(l.iterator(), f);
    assertTrue(i.hasNext());
    assertEquals(new Integer(126), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(50), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(68), i.next());
    assertFalse(i.hasNext());
  }
}
