package prover.gui.builder.tagger;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Iterator;



public class TagTable implements Iterator, Serializable {
	/** */
	private static final long serialVersionUID = 1L;
	private ArrayList al = new ArrayList();
	private TagFile current;
	private Iterator iter;
	private int pos = 0;
	
	private static final class TagFile implements Serializable {
		/** */
		private static final long serialVersionUID = 1L;
		public final String name;
		public final TagStruct [] ts;
		public TagFile(String n, TagList l) {
			name = n;
			Iterator iter = l.iterator();
			ts = new TagStruct[l.al.size()];
			for(int i = 0; iter.hasNext(); i++) {
				ts[i] = (TagStruct)iter.next();
			}
		}
		public TagFile(String n) {
			name = n;
			ts = new TagStruct[0];
		}
		public boolean equals(Object o) {
			return (o != null) && (o instanceof TagFile) && ((TagFile) o).name.equals(name);
		}
		public int hashCode() {
			return name.hashCode();
		}
		public Iterator iterator() {
			return new Iterator() {
				int pos;
				public void remove() {
					
				}

				public boolean hasNext() {
					return pos < ts.length;
				}

				public Object next() {
					return ts[pos++];
				}
				
			};
			
		}
	}
	public static final class TagList{
		private final ArrayList al = new ArrayList();
		public void add(TagStruct ts) {
			al.add(ts);
		}
		public Iterator iterator() {
			return al.iterator();
		}
		public void add(String str, int wordbeg, int i, String filename) {
			add(new TagStruct(str, wordbeg, i, filename));
		}
		
	}
	
	
	public void add(String name, TagList tags) {
		TagFile  tf = new TagFile(name, tags);
		if((current != null) && current.equals(tf)) {
			al.set(pos, tf);
			current = tf;
			iter = tf.iterator();
		}
		else {
			int ind; 
			if ((ind = al.indexOf(tf)) != -1) {
				al.set(ind, tf);
			}
			else {
				al.add(tf);
				if(current == null) {
					iter = tf.iterator();
					current = tf;
				}
			}
		}
		
	}
	public void remove(String name) {
		int ind; 
		if ((ind = al.indexOf(new TagFile(name))) != -1) {
			al.remove(ind);
		}
	}
	
	public void load(ObjectInputStream ois) throws IOException {
		try {
			
			Object [] os = (Object []) ois.readObject();
			al = new ArrayList();
			for(int i= 0; i < os.length; i++) {
				al.add(os[i]);
			}
		}  catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if(al.size() > 0) {
			current = (TagFile)al.get(0);
			iter = current.iterator();
		}
	}
	public void save(ObjectOutputStream oos) throws IOException {
		oos.writeObject(al.toArray());
	}
	
	public void remove() {
		throw new UnsupportedOperationException();
	}

	public boolean hasNext() {
		if(current == null)
			return false;
		if(iter.hasNext()) {
			return true;
		}
		else {
			getNext();
			if(pos == 0)
				return false;
			return iter.hasNext();
		}
	}
	
	private void getNext() {
		if(al.size() > 0) {
			pos ++;
			pos %= al.size();
			current = (TagFile)al.get(pos);
			iter = current.iterator();
		}
	}
	public Object next() {
		return iter.next();
	}
}
