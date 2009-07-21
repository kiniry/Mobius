package mobius.cct.util;

/**
 * Immutable pair.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <L> Type of first element.
 * @param <R> Type of second element.
 */
public final class Pair<L, R> {
  /**
   * Value used to compute hash code.
   */
  private static final int HASH_FACTOR = 0xBABEDEAF;
  
  /**
   * First element.
   */
  private final L fFirst;
  
  /**
   * Second element.
   */
  private final R fSecond;
  
  /**
   * Constructor.
   * @param car First element.
   * @param cdr Second element.
   */
  public Pair(final L car, final R cdr) {
    fFirst = car;
    fSecond = cdr;
  }
  
  /**
   * Get first element.
   * @return First element.
   */
  public L getFirst() {
    return fFirst;
  }
  
  /**
   * Get second element.
   * @return Second element.
   */
  public R getSecond() {
    return fSecond;
  }
  
  /**
   * Get hash code.
   * @return Hash code.
   */
  @Override
  public int hashCode() {
    return getHash(fFirst) + HASH_FACTOR * getHash(fSecond);
  }
  
  /**
   * Test equality.
   * @param o Object.
   * @return .
   */
  @Override
  public boolean equals(final Object o) {
    if (o instanceof Pair) {
      return eq(fFirst, ((Pair<?, ?>)o).getFirst()) &&
      eq(fSecond, ((Pair<?, ?>)o).getSecond());
    } else {
      return false;
    }
  }
  
  /**
   * Get hashCode of object or 0, if the object is null.
   * @param o Object.
   * @return Hash.
   */
  private static int getHash(final Object o) {
    if (o == null) {
      return 0;
    } else {
      return o.hashCode();
    }
  }
  
  /**
   * Compare two object.
   * @param a First object.
   * @param b Second object.
   * @return true if either a.equals(b) and 
   * b.equals(a) or a and b are null.
   */
  private static boolean eq(final Object a, final Object b) {
    if (a == null) {
      return b == null;
    } else {
      if (b == null) {
        return false;
      } else {
        return a.equals(b) && b.equals(a);
      }
    }
  }
}
