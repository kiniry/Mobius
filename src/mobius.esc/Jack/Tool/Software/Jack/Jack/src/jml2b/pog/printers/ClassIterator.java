package jml2b.pog.printers;

import java.util.HashSet;
import java.util.Iterator;

import jml2b.structure.java.AClass;

public class ClassIterator extends AClassEnumeration{

	private Iterator iter;
	
	public ClassIterator(HashSet hs) {
		iter = hs.iterator();
	}
	public boolean hasMoreElements() {
		return iter.hasNext();
	}

	public AClass nextElement() {
		return (AClass) iter.next();
	}

}
