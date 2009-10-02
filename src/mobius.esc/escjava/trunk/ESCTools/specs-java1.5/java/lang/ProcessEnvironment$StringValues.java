package java.lang;

import java.io.*;
import java.util.*;

class ProcessEnvironment$StringValues extends AbstractCollection {
    
    /*synthetic*/ static Collection access$700(ProcessEnvironment$StringValues x0) {
        return x0.c;
    }
    private final Collection c;
    
    public ProcessEnvironment$StringValues(Collection c) {
        
        this.c = c;
    }
    
    public int size() {
        return c.size();
    }
    
    public boolean isEmpty() {
        return c.isEmpty();
    }
    
    public void clear() {
        c.clear();
    }
    
    public Iterator iterator() {
        return new ProcessEnvironment$StringValues$1(this);
    }
    
    public boolean contains(Object o) {
        return c.contains(ProcessEnvironment$Value.valueOfQueryOnly(o));
    }
    
    public boolean remove(Object o) {
        return c.remove(ProcessEnvironment$Value.valueOfQueryOnly(o));
    }
    
    public boolean equals(Object o) {
        return o instanceof ProcessEnvironment$StringValues && c.equals(((ProcessEnvironment$StringValues)(ProcessEnvironment$StringValues)o).c);
    }
    
    public int hashCode() {
        return c.hashCode();
    }
}
