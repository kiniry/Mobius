package bytecode_to_JPO;

import java.util.Collection;
import java.util.HashMap;

import bytecode_wp.vcg.VCGPath;

public class AlreadyCalculatedHypos {
	HashMap fHm = new HashMap();
	
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
	public boolean contains(VCGPath f, int n) {
		if(fHm.containsKey(f)) {
			HashMap col = (HashMap)fHm.get(f);
			return (col.containsKey(new Tuple(n, null)));
		}
		return false;
	}
	public Collection get(VCGPath f, int n) {
		Tuple t = new Tuple(n, null);
		if(fHm.containsKey(f)) {
			HashMap col = (HashMap)fHm.get(f);
			return ((Tuple)col.get(t)).fHypos;		
		}
		return null;
	}
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
