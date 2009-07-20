package bytecode_to_JPO;

import java.util.Collection;
import java.util.HashMap;

import bytecode_wp.vcg.VCGPath;

public class AlreadyCalculatedHypos {
	/** for a path the hypos binded to it */
	HashMap fHm = new HashMap();
	
	
	/**
	 * Add the hypos associated to the path.
	 * @param f the path
	 * @param n the goal number
	 * @param hypos the hypothesis to add
	 */
	public void add(VCGPath f, int n, Collection hypos) {
		Tuple t = new Tuple(n, hypos);
		if(fHm.containsKey(f)) {
			HashMap col = (HashMap)fHm.get(f);
			if(!col.containsKey(t)) {
				col.put(t, t);
			}
		}
		else {
			HashMap al = new HashMap();
			al.put(t, t);
			fHm.put(f, al);
		}
	}
	
	/**
	 * An oracle to tell if the path/goal number structure is already contained
	 * herein.
	 * @param f the path
	 * @param n the goal number
	 * @return sometimes <code>true</code>
	 */
	public boolean contains(VCGPath f, int n) {
		if(fHm.containsKey(f)) {
			HashMap col = (HashMap)fHm.get(f);
			return (col.containsKey(new Tuple(n, null)));
		}
		return false;
	}
	
	/**
	 * Returns the hypothesis belonging to a given path
	 * @param f the 'pathways'
	 * @param n the goal
	 * @return a collection or <code>null</code> if nothing has been found
	 */
	public Collection get(VCGPath f, int n) {
		Tuple t = new Tuple(n, null);
		if(fHm.containsKey(f)) {
			HashMap col = (HashMap)fHm.get(f);
			return ((Tuple)col.get(t)).fHypos;		
		}
		return null;
	}
	
	
	/**
	 * Internal representation of THINGS.
	 * And I give crooked crosses to the nodding God.
	 * Everything is LOVE LOVE LOVE
	 * And all my love is HATE HATE HATE
	 * LOVE is nothing as LOVE is LOVE is LOVE is LOVE is...
	 * @author J. Charles
	 */
	private class Tuple{
		int fNum;
		Collection fHypos;
		public Tuple(int n, Collection hypos) {
			fNum = n;
			fHypos = hypos;
		}
		public int hashCode() {
			return fNum;
		}
		public boolean equals(Object o) {
			return (o instanceof Tuple) && fNum == o.hashCode();
		}
	}
}
