package javax.swing;

import java.util.Enumeration;

class MultiUIDefaults$MultiUIDefaultsEnumerator implements Enumeration {
    Enumeration[] enums;
    int n = 0;
    
    MultiUIDefaults$MultiUIDefaultsEnumerator(Enumeration[] enums) {
        
        this.enums = enums;
    }
    
    public boolean hasMoreElements() {
        for (int i = n; i < enums.length; i++) {
            Enumeration e = enums[i];
            if ((e != null) && (e.hasMoreElements())) {
                return true;
            }
        }
        return false;
    }
    
    public Object nextElement() {
        for (; n < enums.length; n++) {
            Enumeration e = enums[n];
            if ((e != null) && (e.hasMoreElements())) {
                return e.nextElement();
            }
        }
        return null;
    }
}
