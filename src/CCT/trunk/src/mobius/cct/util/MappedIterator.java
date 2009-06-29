package mobius.cct.util;

import java.util.Iterator;

/**
 * An Iterator that applies a mapping function to each value 
 * returned by the source iterator.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <O> Type of values returned by the original iterator.
 * @param <R> Result type of the mapping function.
 */
public class MappedIterator<O, R> implements Iterator<R> {
  /**
   * Source iterator.
   */
  private final Iterator<? extends O> fSource;
  
  /**
   * Mapping function.
   */
  private final Function<? super O, ? extends R> fMapping;
  
  /**
   * Constructor.
   * @param source Source iterator.
   * @param mapping Mapping function.
   */
  public MappedIterator(final Iterator<? extends O> source, 
                        final Function<? super O, ? extends R> mapping) {
    fSource = source;
    fMapping = mapping;
  }

  /**
   * Delegated to the source iterator.
   * @return True iff there is at least one more element in the iterator.
   */
  public boolean hasNext() {
    return fSource.hasNext();
  }

  /**
   * Return next element. The element is taken from the source
   * operator and processed by the mapping function.
   * @return Next element.
   */
  public R next() {
    return fMapping.call(fSource.next());
  }

  /**
   * Delegated to the source iterator.
   */
  public void remove() {
    fSource.remove();
  }
  
}
