package java.util;

public class HashSet extends AbstractSet implements Set, Cloneable, java.io.Serializable {
    static final long serialVersionUID = -5024744406713321676L;
    private transient HashMap map;
    private static final Object PRESENT = new Object();
    
    public HashSet() {
        
        map = new HashMap();
    }
    
    public HashSet(Collection c) {
        
        map = new HashMap(Math.max((int)(c.size() / 0.75F) + 1, 16));
        addAll(c);
    }
    
    public HashSet(int initialCapacity, float loadFactor) {
        
        map = new HashMap(initialCapacity, loadFactor);
    }
    
    public HashSet(int initialCapacity) {
        
        map = new HashMap(initialCapacity);
    }
    
    HashSet(int initialCapacity, float loadFactor, boolean dummy) {
        
        map = new LinkedHashMap(initialCapacity, loadFactor);
    }
    
    public Iterator iterator() {
        return map.keySet().iterator();
    }
    
    public int size() {
        return map.size();
    }
    
    public boolean isEmpty() {
        return map.isEmpty();
    }
    
    public boolean contains(Object o) {
        return map.containsKey(o);
    }
    
    public boolean add(Object o) {
        return map.put(o, PRESENT) == null;
    }
    
    public boolean remove(Object o) {
        return map.remove(o) == PRESENT;
    }
    
    public void clear() {
        map.clear();
    }
    
    public Object clone() {
        try {
            HashSet newSet = (HashSet)(HashSet)super.clone();
            newSet.map = (HashMap)(HashMap)map.clone();
            return newSet;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(map.capacity());
        s.writeFloat(map.loadFactor());
        s.writeInt(map.size());
        for (Iterator i = map.keySet().iterator(); i.hasNext(); ) s.writeObject(i.next());
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        int capacity = s.readInt();
        float loadFactor = s.readFloat();
        map = (((HashSet)this) instanceof LinkedHashSet ? new LinkedHashMap(capacity, loadFactor) : new HashMap(capacity, loadFactor));
        int size = s.readInt();
        for (int i = 0; i < size; i++) {
            Object e = (Object)s.readObject();
            map.put(e, PRESENT);
        }
    }
}
