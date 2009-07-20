package mobius.prover.gui.builder.tagger;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * A list of tags. The only thing you can do with it
 * is add some tags, and read all the tags using an iterator.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class TagList implements Iterable<TagStruct> {
  /** the list containing the tags. */
  private final List<TagStruct> fList = new ArrayList<TagStruct>();
  
  /** 
   * Add a tag structure to the list.
   * @param ts the tag to add 
   */
  public void add(final TagStruct ts) {
    fList.add(ts);
  }
  
  /**
   * Returns the size of the list.
   * @return a number greater or equal than 0
   */
  public int size() {
    return fList.size();
  }
  
  
  /** 
   * Return the iterator of the tag list.
   * @return an iterator 
   */
  public Iterator<TagStruct> iterator() {
    return fList.iterator();
  } 
  
}
