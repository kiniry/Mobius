package java.util;

public class TreeSet extends AbstractSet implements SortedSet, Cloneable, java.io.Serializable {
    private transient SortedMap m;
    private transient Set keySet;
    private static final Object PRESENT = new Object();
    
    private TreeSet(SortedMap m) {
        
        this.m = m;
        keySet = m.keySet();
    }
    
    public TreeSet() {
        this(new TreeMap());
    }
    
    public TreeSet(Comparator c) {
        this(new TreeMap(c));
    }
    
    public TreeSet(Collection c) {
        this();
        addAll(c);
    }
    
    public TreeSet(SortedSet s) {
        this(s.comparator());
        addAll(s);
    }
    
    public Iterator iterator() {
        return keySet.iterator();
    }
    
    public int size() {
        return m.size();
    }
    
    public boolean isEmpty() {
        return m.isEmpty();
    }
    
    public boolean contains(Object o) {
        return m.containsKey(o);
    }
    
    public boolean add(Object o) {
        return m.put(o, PRESENT) == null;
    }
    
    public boolean remove(Object o) {
        return m.remove(o) == PRESENT;
    }
    
    public void clear() {
        m.clear();
    }
    
    public boolean addAll(Collection c) {
        if (m.size() == 0 && c.size() > 0 && c instanceof SortedSet && m instanceof TreeMap) {
            SortedSet set = (SortedSet)(SortedSet)(SortedSet)c;
            TreeMap map = (TreeMap)(TreeMap)m;
            Comparator cc = (Comparator)set.comparator();
            Comparator mc = map.comparator();
            if (cc == mc || (cc != null && cc.equals(mc))) {
                map.addAllForTreeSet(set, PRESENT);
                return true;
            }
        }
        return super.addAll(c);
    }
    
    public SortedSet subSet(Object fromElement, Object toElement) {
        return new TreeSet(m.subMap(fromElement, toElement));
    }
    
    public SortedSet headSet(Object toElement) {
        return new TreeSet(m.headMap(toElement));
    }
    
    public SortedSet tailSet(Object fromElement) {
        return new TreeSet(m.tailMap(fromElement));
    }
    
    public Comparator comparator() {
        return m.comparator();
    }
    
    public Object first() {
        return m.firstKey();
    }
    
    public Object last() {
        return m.lastKey();
    }
    
    public Object clone() {
        TreeSet clone = null;
        try {
            clone = (TreeSet)(TreeSet)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
        clone.m = new TreeMap(m);
        clone.keySet = clone.m.keySet();
        return clone;
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeObject(m.comparator());
        s.writeInt(m.size());
        for (Iterator i = m.keySet().iterator(); i.hasNext(); ) s.writeObject(i.next());
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        Comparator c = (Comparator)(Comparator)s.readObject();
        TreeMap tm;
        if (c == null) tm = new TreeMap(); else tm = new TreeMap(c);
        m = tm;
        keySet = m.keySet();
        int size = s.readInt();
        tm.readTreeSet(size, s, PRESENT);
    }
    private static final long serialVersionUID = -2479143000061671589L;
}
