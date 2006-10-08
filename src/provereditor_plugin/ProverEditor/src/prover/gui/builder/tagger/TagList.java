package prover.gui.builder.tagger;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * A list of tags. The only thing you can do with it
 * is add some tags, and read all the tags using an iterator.
 * @author J. Charles
 */
public final class TagList{
	/** the list containing the tags */
	final List list = new ArrayList();
	
	/** add a tag structure to the list */
	public void add(TagStruct ts) {
		list.add(ts);
	}
	
	/** return the iterator of the tag list */
	public Iterator iterator() {
		return list.iterator();
	}
	
	
}