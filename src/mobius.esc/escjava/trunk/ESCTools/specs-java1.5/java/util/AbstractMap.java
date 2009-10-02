package java.util;

import java.util.Map.Entry;

public abstract class AbstractMap implements Map {
    
    protected AbstractMap() {
        
    }
    
    public int size() {
        return entrySet().size();
    }
    
    public boolean isEmpty() {
        return size() == 0;
    }
    
    public boolean containsValue(Object value) {
        Iterator i = entrySet().iterator();
        if (value == null) {
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (e.getValue() == null) return true;
            }
        } else {
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (value.equals(e.getValue())) return true;
            }
        }
        return false;
    }
    
    public boolean containsKey(Object key) {
        Iterator i = entrySet().iterator();
        if (key == null) {
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (e.getKey() == null) return true;
            }
        } else {
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (key.equals(e.getKey())) return true;
            }
        }
        return false;
    }
    
    public Object get(Object key) {
        Iterator i = entrySet().iterator();
        if (key == null) {
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (e.getKey() == null) return e.getValue();
            }
        } else {
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (key.equals(e.getKey())) return e.getValue();
            }
        }
        return null;
    }
    
    public Object put(Object key, Object value) {
        throw new UnsupportedOperationException();
    }
    
    public Object remove(Object key) {
        Iterator i = entrySet().iterator();
        Map$Entry correctEntry = null;
        if (key == null) {
            while (correctEntry == null && i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (e.getKey() == null) correctEntry = e;
            }
        } else {
            while (correctEntry == null && i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                if (key.equals(e.getKey())) correctEntry = e;
            }
        }
        Object oldValue = null;
        if (correctEntry != null) {
            oldValue = correctEntry.getValue();
            i.remove();
        }
        return oldValue;
    }
    
    public void putAll(Map t) {
        Iterator i = t.entrySet().iterator();
        while (i.hasNext()) {
            Map$Entry e = (Map$Entry)i.next();
            put(e.getKey(), e.getValue());
        }
    }
    
    public void clear() {
        entrySet().clear();
    }
    volatile transient Set keySet = null;
    volatile transient Collection values = null;
    
    public Set keySet() {
        if (keySet == null) {
            keySet = new AbstractMap$1(this);
        }
        return keySet;
    }
    
    public Collection values() {
        if (values == null) {
            values = new AbstractMap$2(this);
        }
        return values;
    }
    
    public abstract Set entrySet();
    
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Map)) return false;
        Map t = (Map)(Map)o;
        if (t.size() != size()) return false;
        try {
            Iterator i = entrySet().iterator();
            while (i.hasNext()) {
                Map$Entry e = (Map$Entry)i.next();
                Object key = e.getKey();
                Object value = e.getValue();
                if (value == null) {
                    if (!(t.get(key) == null && t.containsKey(key))) return false;
                } else {
                    if (!value.equals(t.get(key))) return false;
                }
            }
        } catch (ClassCastException unused) {
            return false;
        } catch (NullPointerException unused) {
            return false;
        }
        return true;
    }
    
    public int hashCode() {
        int h = 0;
        Iterator i = entrySet().iterator();
        while (i.hasNext()) h += ((Map$Entry)i.next()).hashCode();
        return h;
    }
    
    public String toString() {
        StringBuffer buf = new StringBuffer();
        buf.append("{");
        Iterator i = entrySet().iterator();
        boolean hasNext = i.hasNext();
        while (hasNext) {
            Map$Entry e = (Map$Entry)i.next();
            Object key = e.getKey();
            Object value = e.getValue();
            if (key == this) buf.append("(this Map)"); else buf.append(key);
            buf.append("=");
            if (value == this) buf.append("(this Map)"); else buf.append(value);
            hasNext = i.hasNext();
            if (hasNext) buf.append(", ");
        }
        buf.append("}");
        return buf.toString();
    }
    
    protected Object clone() throws CloneNotSupportedException {
        AbstractMap result = (AbstractMap)(AbstractMap)super.clone();
        result.keySet = null;
        result.values = null;
        return result;
    }
    {
    }
}
