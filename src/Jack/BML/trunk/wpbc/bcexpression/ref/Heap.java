/*
 * Created on Apr 27, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.ref;

import java.util.HashMap;

/**
 * @author mpavlova
 *
 * the class models a heap for this method
 */
public class Heap {
	HashMap heap;
	
	
	public Heap() {
		
	}
	
	protected void initHeap( ) {
		heap = new HashMap();
	}
	
	public void  addReference(int _i, Reference _ref) {
			if (heap == null) {
				initHeap();
			}
			heap.put( new Integer(_i), _ref);
		
	}
	
	public Reference getReference(int _i ) {
		Integer index = new Integer( _i);
		if  (heap == null)  {
			return null;
		}
		Reference ref  = (Reference)heap.get( index);
		return ref;
	}
}
