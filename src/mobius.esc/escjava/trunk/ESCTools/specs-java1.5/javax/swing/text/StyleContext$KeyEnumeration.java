package javax.swing.text;

import java.awt.*;
import java.util.*;
import java.io.*;

class StyleContext$KeyEnumeration implements Enumeration {
    /*synthetic*/ final StyleContext this$0;
    
    StyleContext$KeyEnumeration(/*synthetic*/ final StyleContext this$0, Object[] attr) {
        this.this$0 = this$0;
        
        this.attr = attr;
        i = 0;
    }
    
    public boolean hasMoreElements() {
        return i < attr.length;
    }
    
    public Object nextElement() {
        if (i < attr.length) {
            Object o = attr[i];
            i += 2;
            return o;
        }
        throw new NoSuchElementException();
    }
    Object[] attr;
    int i;
}
