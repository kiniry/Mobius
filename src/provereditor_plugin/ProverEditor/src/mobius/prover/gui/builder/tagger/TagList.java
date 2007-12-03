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
  final List<TagStruct> list = new ArrayList<TagStruct>();
  
  /** add a tag structure to the list. */
  public void add(final TagStruct ts) {
    list.add(ts);
  }
  
  /** return the iterator of the tag list. */
  public Iterator<TagStruct> iterator() {
    return list.iterator();
  } 
  
}
