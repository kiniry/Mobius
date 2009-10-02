package javax.swing.text;

import java.awt.*;
import java.util.*;
import java.io.*;

class StyleContext$KeyBuilder {
    /*synthetic*/ final StyleContext this$0;
    
    StyleContext$KeyBuilder(/*synthetic*/ final StyleContext this$0) {
        this.this$0 = this$0;
        
    }
    
    public void initialize(AttributeSet a) {
        if (a instanceof StyleContext$SmallAttributeSet) {
            initialize(((StyleContext$SmallAttributeSet)(StyleContext$SmallAttributeSet)a).attributes);
        } else {
            keys.removeAllElements();
            data.removeAllElements();
            Enumeration names = a.getAttributeNames();
            while (names.hasMoreElements()) {
                Object name = names.nextElement();
                addAttribute(name, a.getAttribute(name));
            }
        }
    }
    
    private void initialize(Object[] sorted) {
        keys.removeAllElements();
        data.removeAllElements();
        int n = sorted.length;
        for (int i = 0; i < n; i += 2) {
            keys.addElement(sorted[i]);
            data.addElement(sorted[i + 1]);
        }
    }
    
    public Object[] createTable() {
        int n = keys.size();
        Object[] tbl = new Object[2 * n];
        for (int i = 0; i < n; i++) {
            int offs = 2 * i;
            tbl[offs] = keys.elementAt(i);
            tbl[offs + 1] = data.elementAt(i);
        }
        return tbl;
    }
    
    int getCount() {
        return keys.size();
    }
    
    public void addAttribute(Object key, Object value) {
        keys.addElement(key);
        data.addElement(value);
    }
    
    public void addAttributes(AttributeSet attr) {
        if (attr instanceof StyleContext$SmallAttributeSet) {
            Object[] tbl = ((StyleContext$SmallAttributeSet)(StyleContext$SmallAttributeSet)attr).attributes;
            int n = tbl.length;
            for (int i = 0; i < n; i += 2) {
                addAttribute(tbl[i], tbl[i + 1]);
            }
        } else {
            Enumeration names = attr.getAttributeNames();
            while (names.hasMoreElements()) {
                Object name = names.nextElement();
                addAttribute(name, attr.getAttribute(name));
            }
        }
    }
    
    public void removeAttribute(Object key) {
        int n = keys.size();
        for (int i = 0; i < n; i++) {
            if (keys.elementAt(i).equals(key)) {
                keys.removeElementAt(i);
                data.removeElementAt(i);
                return;
            }
        }
    }
    
    public void removeAttributes(Enumeration names) {
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            removeAttribute(name);
        }
    }
    
    public void removeAttributes(AttributeSet attr) {
        Enumeration names = attr.getAttributeNames();
        while (names.hasMoreElements()) {
            Object name = names.nextElement();
            Object value = attr.getAttribute(name);
            removeSearchAttribute(name, value);
        }
    }
    
    private void removeSearchAttribute(Object ikey, Object value) {
        int n = keys.size();
        for (int i = 0; i < n; i++) {
            if (keys.elementAt(i).equals(ikey)) {
                if (data.elementAt(i).equals(value)) {
                    keys.removeElementAt(i);
                    data.removeElementAt(i);
                }
                return;
            }
        }
    }
    private Vector keys = new Vector();
    private Vector data = new Vector();
}
