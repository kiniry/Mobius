package java.util;

class ResourceBundleEnumeration implements Enumeration {
    Set set;
    Iterator iterator;
    Enumeration enumeration;
    
    ResourceBundleEnumeration(Set set, Enumeration enumeration) {
        
        this.set = set;
        this.iterator = set.iterator();
        this.enumeration = enumeration;
    }
    String next = null;
    
    public boolean hasMoreElements() {
        if (next == null) {
            if (iterator.hasNext()) {
                next = (String)iterator.next();
            } else if (enumeration != null) {
                while (next == null && enumeration.hasMoreElements()) {
                    next = (String)enumeration.nextElement();
                    if (set.contains(next)) {
                        next = null;
                    }
                }
            }
        }
        return next != null;
    }
    
    public String nextElement() {
        if (hasMoreElements()) {
            String result = next;
            next = null;
            return result;
        } else {
            throw new NoSuchElementException();
        }
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
