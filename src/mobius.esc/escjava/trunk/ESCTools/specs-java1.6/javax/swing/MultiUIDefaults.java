package javax.swing;

import java.util.Enumeration;
import java.util.Locale;

class MultiUIDefaults extends UIDefaults {
    private UIDefaults[] tables;
    
    public MultiUIDefaults(UIDefaults[] defaults) {
        
        tables = defaults;
    }
    
    public MultiUIDefaults() {
        
        tables = new UIDefaults[0];
    }
    
    public Object get(Object key) {
        Object value = super.get(key);
        if (value != null) {
            return value;
        }
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            value = (table != null) ? table.get(key) : null;
            if (value != null) {
                return value;
            }
        }
        return null;
    }
    
    public Object get(Object key, Locale l) {
        Object value = super.get(key, l);
        if (value != null) {
            return value;
        }
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            value = (table != null) ? table.get(key, l) : null;
            if (value != null) {
                return value;
            }
        }
        return null;
    }
    
    public int size() {
        int n = super.size();
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            n += (table != null) ? table.size() : 0;
        }
        return n;
    }
    
    public boolean isEmpty() {
        return size() == 0;
    }
    
    public Enumeration keys() {
        Enumeration[] enums = new Enumeration[1 + tables.length];
        enums[0] = super.keys();
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            if (table != null) {
                enums[i + 1] = table.keys();
            }
        }
        return new MultiUIDefaults$MultiUIDefaultsEnumerator(enums);
    }
    
    public Enumeration elements() {
        Enumeration[] enums = new Enumeration[1 + tables.length];
        enums[0] = super.elements();
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            if (table != null) {
                enums[i + 1] = table.elements();
            }
        }
        return new MultiUIDefaults$MultiUIDefaultsEnumerator(enums);
    }
    
    protected void getUIError(String msg) {
        if (tables.length > 0) {
            tables[0].getUIError(msg);
        } else {
            super.getUIError(msg);
        }
    }
    {
    }
    
    public Object remove(Object key) {
        Object value = super.remove(key);
        if (value != null) {
            return value;
        }
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            value = (table != null) ? table.remove(key) : null;
            if (value != null) {
                return value;
            }
        }
        return null;
    }
    
    public void clear() {
        super.clear();
        for (int i = 0; i < tables.length; i++) {
            UIDefaults table = tables[i];
            if (table != null) {
                table.clear();
            }
        }
    }
    
    public synchronized String toString() {
        StringBuffer buf = new StringBuffer();
        buf.append("{");
        Enumeration keys = keys();
        while (keys.hasMoreElements()) {
            Object key = keys.nextElement();
            buf.append(key + "=" + get(key) + ", ");
        }
        int length = buf.length();
        if (length > 1) {
            buf.delete(length - 2, length);
        }
        buf.append("}");
        return buf.toString();
    }
}
