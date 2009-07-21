package mobius.cct.tests.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import mobius.cct.util.ArrayIterator;

import org.junit.Before;
import org.junit.Test;

/**
 * Tests for class mobius.cct.util.ArrayIterator.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ArrayIteratorTest {
  /**
   * Array used in tests.
   */
  private Integer[] fArray;
  
  /**
   * Method called before each test.
   */
  @Before
  public void setUp() {
    fArray = new Integer[] { 0, 1, 2, 3, 4, 5, 6 };
  }
  
  /**
   * Simple positive test.
   */
  @Test
  public void testNormal() {
    int i;
    
    ArrayIterator<Integer> it = new ArrayIterator<Integer>(fArray);
    for (i = 0; i < fArray.length; i++) {
      assertTrue(it.hasNext());
      assertEquals(fArray[i], it.next());
    }
    assertFalse(it.hasNext());
  }
  
  /**
   * Test iteration over range of indices.
   */
  @Test
  public void testRange() {
    int i;
    
    ArrayIterator<Integer> it = new ArrayIterator<Integer>(fArray, 2, 4);
    for (i = 2; i < 4; i++) {
      assertTrue(it.hasNext());
      assertEquals(fArray[i], it.next());
    }
    assertFalse(it.hasNext());
  }
  
  /**
   * Invalid start index.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testNegativeStart() {
    new ArrayIterator<Integer>(fArray, -42);
  }
  
  /**
   * Start index greater than array length.
   */
  @Test
  public void testEmpty() {
    ArrayIterator<Integer> it = 
      new ArrayIterator<Integer>(fArray, fArray.length + 3);
    assertFalse(it.hasNext());
  }
  

  /**
   * Bound index greater than array length.
   */
  @Test
  public void testBound() {
    int i;
    
    ArrayIterator<Integer> it = 
      new ArrayIterator<Integer>(fArray, 0, fArray.length + 3);
    for (i = 0; i < fArray.length; i++) {
      assertTrue(it.hasNext());
      assertEquals(fArray[i], it.next());
    }
    assertFalse(it.hasNext());
  }
  
  /**
   * Test null array.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testNull1() {
    new ArrayIterator<Integer>(null);
  }

  /**
   * Test null array.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testNull2() {
    new ArrayIterator<Integer>(null, 0);
  }

  /**
   * Test null array.
   */
  @Test(expected=IllegalArgumentException.class)
  public void testNull3() {
    new ArrayIterator<Integer>(null, 0, 1);
  }
  
  /**
   * Test remove().
   */
  @Test(expected=UnsupportedOperationException.class)
  public void testRemove() {
    new ArrayIterator<Integer>(fArray).remove();
  }
  
}
