package javax.swing.text;

import java.awt.*;
import java.util.*;
import java.io.*;

class StyleContext$FontKey {
    private String family;
    private int style;
    private int size;
    
    public StyleContext$FontKey(String family, int style, int size) {
        
        setValue(family, style, size);
    }
    
    public void setValue(String family, int style, int size) {
        this.family = (family != null) ? family.intern() : null;
        this.style = style;
        this.size = size;
    }
    
    public int hashCode() {
        int fhash = (family != null) ? family.hashCode() : 0;
        return fhash ^ style ^ size;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof StyleContext$FontKey) {
            StyleContext$FontKey font = (StyleContext$FontKey)(StyleContext$FontKey)obj;
            return (size == font.size) && (style == font.style) && (family == font.family);
        }
        return false;
    }
}
