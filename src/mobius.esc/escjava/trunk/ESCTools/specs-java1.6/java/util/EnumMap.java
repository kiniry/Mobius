package java.util;

import java.util.Map.Entry;

public class EnumMap extends AbstractMap implements java.io.Serializable, Cloneable {
    
    /*synthetic*/ static Object access$1400() {
        return NULL;
    }
    
    /*synthetic*/ static Object access$1200(EnumMap x0, Object x1) {
        return x0.unmaskNull(x1);
    }
    
    /*synthetic*/ static Enum[] access$1100(EnumMap x0) {
        return x0.keyUniverse;
    }
    
    /*synthetic*/ static boolean access$1000(EnumMap x0, Object x1, Object x2) {
        return x0.removeMapping(x1, x2);
    }
    
    /*synthetic*/ static boolean access$900(EnumMap x0, Object x1, Object x2) {
        return x0.containsMapping(x1, x2);
    }
    
    /*synthetic*/ static Object[] access$600(EnumMap x0) {
        return x0.vals;
    }
    
    /*synthetic*/ static Object access$500(EnumMap x0, Object x1) {
        return x0.maskNull(x1);
    }
    
    /*synthetic*/ static int access$210(EnumMap x0) {
        return x0.size--;
    }
    
    /*synthetic*/ static int access$200(EnumMap x0) {
        return x0.size;
    }
    {
    }
    private final Class keyType;
    private transient Enum[] keyUniverse;
    private transient Object[] vals;
    private transient int size = 0;
    private static final Object NULL = new Object();
    
    private Object maskNull(Object value) {
        return (value == null ? NULL : value);
    }
    
    private Object unmaskNull(Object value) {
        return (Object)(value == NULL ? null : value);
    }
    private static Enum[] ZERO_LENGTH_ENUM_ARRAY = new Enum[0];
    
    public EnumMap(Class keyType) {
        
        this.keyType = keyType;
        keyUniverse = (Enum[])keyType.getEnumConstants();
        vals = new Object[keyUniverse.length];
    }
    
    public EnumMap(EnumMap m) {
        
        keyType = m.keyType;
        keyUniverse = m.keyUniverse;
        vals = (Object[])(Object[])m.vals.clone();
        size = m.size;
    }
    
    public EnumMap(Map m) {
        
        if (m instanceof EnumMap) {
            EnumMap em = (EnumMap)(EnumMap)m;
            keyType = em.keyType;
            keyUniverse = em.keyUniverse;
            vals = (Object[])(Object[])em.vals.clone();
            size = em.size;
        } else {
            if (m.isEmpty()) throw new IllegalArgumentException("Specified map is empty");
            keyType = ((Enum)m.keySet().iterator().next()).getDeclaringClass();
            keyUniverse = (Enum[])keyType.getEnumConstants();
            vals = new Object[keyUniverse.length];
            putAll(m);
        }
    }
    
    public int size() {
        return size;
    }
    
    public boolean containsValue(Object value) {
        value = maskNull(value);
        for (Object[] arr$ = vals, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Object val = arr$[i$];
            if (value.equals(val)) return true;
        }
        return false;
    }
    
    public boolean containsKey(Object key) {
        return isValidKey(key) && vals[((Enum)(Enum)key).ordinal()] != null;
    }
    
    private boolean containsMapping(Object key, Object value) {
        return isValidKey(key) && maskNull(value).equals(vals[((Enum)(Enum)key).ordinal()]);
    }
    
    public Object get(Object key) {
        return (isValidKey(key) ? unmaskNull(vals[((Enum)(Enum)key).ordinal()]) : null);
    }
    
    public Object put(Enum key, Object value) {
        typeCheck(key);
        int index = ((Enum)key).ordinal();
        Object oldValue = vals[index];
        vals[index] = maskNull(value);
        if (oldValue == null) size++;
        return unmaskNull(oldValue);
    }
    
    public Object remove(Object key) {
        if (!isValidKey(key)) return null;
        int index = ((Enum)(Enum)key).ordinal();
        Object oldValue = vals[index];
        vals[index] = null;
        if (oldValue != null) size--;
        return unmaskNull(oldValue);
    }
    
    private boolean removeMapping(Object key, Object value) {
        if (!isValidKey(key)) return false;
        int index = ((Enum)(Enum)key).ordinal();
        if (maskNull(value).equals(vals[index])) {
            vals[index] = null;
            size--;
            return true;
        }
        return false;
    }
    
    private boolean isValidKey(Object key) {
        if (key == null) return false;
        Class keyClass = key.getClass();
        return keyClass == keyType || keyClass.getSuperclass() == keyType;
    }
    
    public void putAll(Map m) {
        if (m instanceof EnumMap) {
            EnumMap em = (EnumMap)(EnumMap)m;
            if (em.keyType != keyType) {
                if (em.isEmpty()) return;
                throw new ClassCastException(em.keyType + " != " + keyType);
            }
            for (int i = 0; i < keyUniverse.length; i++) {
                Object emValue = em.vals[i];
                if (emValue != null) {
                    if (vals[i] == null) size++;
                    vals[i] = emValue;
                }
            }
        } else {
            super.putAll(m);
        }
    }
    
    public void clear() {
        Arrays.fill(vals, null);
        size = 0;
    }
    private transient Set entrySet = null;
    
    public Set keySet() {
        Set ks = keySet;
        if (ks != null) return ks; else return keySet = new EnumMap$KeySet(this, null);
    }
    {
    }
    
    public Collection values() {
        Collection vs = values;
        if (vs != null) return vs; else return values = new EnumMap$Values(this, null);
    }
    {
    }
    
    public Set entrySet() {
        Set es = entrySet;
        if (es != null) return es; else return entrySet = new EnumMap$EntrySet(this, null);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof EnumMap)) return super.equals(o);
        EnumMap em = (EnumMap)(EnumMap)o;
        if (em.keyType != keyType) return size == 0 && em.size == 0;
        for (int i = 0; i < keyUniverse.length; i++) {
            Object ourValue = vals[i];
            Object hisValue = em.vals[i];
            if (hisValue != ourValue && (hisValue == null || !hisValue.equals(ourValue))) return false;
        }
        return true;
    }
    
    public EnumMap clone() {
        EnumMap result = null;
        try {
            result = (EnumMap)(EnumMap)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new AssertionError();
        }
        result.vals = (Object[])(Object[])result.vals.clone();
        return result;
    }
    
    private void typeCheck(Enum key) {
        Class keyClass = key.getClass();
        if (keyClass != keyType && keyClass.getSuperclass() != keyType) throw new ClassCastException(keyClass + " != " + keyType);
    }
    private static final long serialVersionUID = 458661240069192865L;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
        s.writeInt(size);
        for (Iterator i$ = entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry e = (Map$Entry)i$.next();
            {
                s.writeObject(e.getKey());
                s.writeObject(e.getValue());
            }
        }
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        keyUniverse = (Enum[])keyType.getEnumConstants();
        vals = new Object[keyUniverse.length];
        int size = s.readInt();
        for (int i = 0; i < size; i++) {
            Enum key = (Enum)(Enum)s.readObject();
            Object value = (Object)s.readObject();
            put(key, value);
        }
    }
    
    /*synthetic public Object clone() throws CloneNotSupportedException {
        return this.clone();
    } */
    
    /*synthetic*/ public Object put(Object x0, Object x1) {
        return this.put((Enum)x0, x1);
    }
}
