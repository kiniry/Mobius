package javax.swing;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Hashtable;

class ArrayTable implements Cloneable {
    
    ArrayTable() {
        
    }
    private Object table = null;
    private static final int ARRAY_BOUNDARY = 8;
    
    static void writeArrayTable(ObjectOutputStream s, ArrayTable table) throws IOException {
        Object[] keys;
        if (table == null || (keys = table.getKeys(null)) == null) {
            s.writeInt(0);
        } else {
            int validCount = 0;
            for (int counter = 0; counter < keys.length; counter++) {
                if ((keys[counter] instanceof Serializable) && (table.get(keys[counter]) instanceof Serializable)) {
                    validCount++;
                } else {
                    keys[counter] = null;
                }
            }
            s.writeInt(validCount);
            if (validCount > 0) {
                for (int counter = 0; counter < keys.length; counter++) {
                    if (keys[counter] != null) {
                        s.writeObject(keys[counter]);
                        s.writeObject(table.get(keys[counter]));
                        if (--validCount == 0) {
                            break;
                        }
                    }
                }
            }
        }
    }
    
    public void put(Object key, Object value) {
        if (table == null) {
            table = new Object[]{key, value};
        } else {
            int size = size();
            if (size < ARRAY_BOUNDARY) {
                if (containsKey(key)) {
                    Object[] tmp = (Object[])(Object[])table;
                    for (int i = 0; i < tmp.length - 1; i += 2) {
                        if (tmp[i].equals(key)) {
                            tmp[i + 1] = value;
                            break;
                        }
                    }
                } else {
                    Object[] array = (Object[])(Object[])table;
                    int i = array.length;
                    Object[] tmp = new Object[i + 2];
                    System.arraycopy(array, 0, tmp, 0, i);
                    tmp[i] = key;
                    tmp[i + 1] = value;
                    table = tmp;
                }
            } else {
                if ((size == ARRAY_BOUNDARY) && isArray()) {
                    grow();
                }
                ((Hashtable)(Hashtable)table).put(key, value);
            }
        }
    }
    
    public Object get(Object key) {
        Object value = null;
        if (table != null) {
            if (isArray()) {
                Object[] array = (Object[])(Object[])table;
                for (int i = 0; i < array.length - 1; i += 2) {
                    if (array[i].equals(key)) {
                        value = array[i + 1];
                        break;
                    }
                }
            } else {
                value = ((Hashtable)(Hashtable)table).get(key);
            }
        }
        return value;
    }
    
    public int size() {
        int size;
        if (table == null) return 0;
        if (isArray()) {
            size = ((Object[])(Object[])table).length / 2;
        } else {
            size = ((Hashtable)(Hashtable)table).size();
        }
        return size;
    }
    
    public boolean containsKey(Object key) {
        boolean contains = false;
        if (table != null) {
            if (isArray()) {
                Object[] array = (Object[])(Object[])table;
                for (int i = 0; i < array.length - 1; i += 2) {
                    if (array[i].equals(key)) {
                        contains = true;
                        break;
                    }
                }
            } else {
                contains = ((Hashtable)(Hashtable)table).containsKey(key);
            }
        }
        return contains;
    }
    
    public Object remove(Object key) {
        Object value = null;
        if (key == null) {
            return null;
        }
        if (table != null) {
            if (isArray()) {
                int index = -1;
                Object[] array = (Object[])(Object[])table;
                for (int i = array.length - 2; i >= 0; i -= 2) {
                    if (array[i].equals(key)) {
                        index = i;
                        value = array[i + 1];
                        break;
                    }
                }
                if (index != -1) {
                    Object[] tmp = new Object[array.length - 2];
                    System.arraycopy(array, 0, tmp, 0, index);
                    if (index < tmp.length) System.arraycopy(array, index + 2, tmp, index, tmp.length - index);
                    table = (tmp.length == 0) ? null : tmp;
                }
            } else {
                value = ((Hashtable)(Hashtable)table).remove(key);
            }
            if (size() == ARRAY_BOUNDARY - 1 && !isArray()) {
                shrink();
            }
        }
        return value;
    }
    
    public void clear() {
        table = null;
    }
    
    public Object clone() {
        ArrayTable newArrayTable = new ArrayTable();
        if (isArray()) {
            Object[] array = (Object[])(Object[])table;
            for (int i = 0; i < array.length - 1; i += 2) {
                newArrayTable.put(array[i], array[i + 1]);
            }
        } else {
            Hashtable tmp = (Hashtable)(Hashtable)table;
            Enumeration keys = tmp.keys();
            while (keys.hasMoreElements()) {
                Object o = keys.nextElement();
                newArrayTable.put(o, tmp.get(o));
            }
        }
        return newArrayTable;
    }
    
    public Object[] getKeys(Object[] keys) {
        if (table == null) {
            return null;
        }
        if (isArray()) {
            Object[] array = (Object[])(Object[])table;
            if (keys == null) {
                keys = new Object[array.length / 2];
            }
            for (int i = 0, index = 0; i < array.length - 1; i += 2, index++) {
                keys[index] = array[i];
            }
        } else {
            Hashtable tmp = (Hashtable)(Hashtable)table;
            Enumeration enum_ = tmp.keys();
            int counter = tmp.size();
            if (keys == null) {
                keys = new Object[counter];
            }
            while (counter > 0) {
                keys[--counter] = enum_.nextElement();
            }
        }
        return keys;
    }
    
    private boolean isArray() {
        return (table instanceof Object[]);
    }
    
    private void grow() {
        Object[] array = (Object[])(Object[])table;
        Hashtable tmp = new Hashtable(array.length / 2);
        for (int i = 0; i < array.length; i += 2) {
            tmp.put(array[i], array[i + 1]);
        }
        table = tmp;
    }
    
    private void shrink() {
        Hashtable tmp = (Hashtable)(Hashtable)table;
        Object[] array = new Object[tmp.size() * 2];
        Enumeration keys = tmp.keys();
        int j = 0;
        while (keys.hasMoreElements()) {
            Object o = keys.nextElement();
            array[j] = o;
            array[j + 1] = tmp.get(o);
            j += 2;
        }
        table = array;
    }
}
