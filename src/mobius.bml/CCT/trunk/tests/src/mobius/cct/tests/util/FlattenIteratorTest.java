package mobius.cct.tests.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;

import mobius.cct.util.FlattenIterator;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for class FlattenIterator.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class FlattenIteratorTest {
  private ArrayList<Integer> l1;
  private ArrayList<Integer> l2;
  private ArrayList<Iterator<Integer>> l;
  private FlattenIterator<Integer> i;
  
  /**
   * Method executed before each test.
   */
  @Before
  public void setUp() {
    l1 = new ArrayList<Integer>();
    l2 = new ArrayList<Integer>();
    l1.add(1);
    l1.add(2);
    l1.add(3);
    l2.add(4);
    l2.add(5);
    l2.add(6);
    l =  new ArrayList<Iterator<Integer>>();

    l.add(l1.iterator());
    l.add(l2.iterator());
    i = new FlattenIterator<Integer>(l.iterator());
  }
  
  /**
   * Test normal behaviour.
   */
  @Test
  public void testNormal() {
    ArrayList<Iterator<Integer>> l = 
      new ArrayList<Iterator<Integer>>();

    l.add(l1.iterator());
    l.add(l2.iterator());
    FlattenIterator<Integer> i = 
      new FlattenIterator<Integer>(l.iterator());
    assertTrue(i.hasNext());
    assertEquals(new Integer(1), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(2), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(3), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(4), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(5), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(6), i.next());
    assertFalse(i.hasNext());
  }
  
  /**
   * Test remove().
   */
  @Test
  public void testRemove() {

    assertTrue(i.hasNext());
    assertEquals(new Integer(1), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(2), i.next());
    assertTrue(i.hasNext());
    assertEquals(new Integer(3), i.next());
    i.remove();
    assertEquals(2, l1.size());
    assertEquals(new Integer(1), l1.get(0));
    assertEquals(new Integer(2), l1.get(1));
  }
  
  /**
   * Test empty iterator.
   */
  @Test(expected=NoSuchElementException.class)
  public void testEmpty() {
    i.next(); i.next(); i.next();
    i.next(); i.next(); i.next();
    i.next();
  }
  
}
